use super::*;

use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{MachineCastSpelling, cast_term};

impl PureFactContext {
    /// Selects exact premises for two terms pinned to the same signed constant.
    /// This query reads the constant-equality index, never the connected facts
    /// of either term. The caller must still check a derivation from the result.
    pub(crate) fn indexed_constant_equality_premises(
        &self,
        proposition: &Proposition,
    ) -> Option<Vec<Proposition>> {
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let Proposition::ConditionIs(condition, value) = proposition else {
            return None;
        };
        let view = comparison_view(condition.old_form(), *value)?;
        if !matches!(
            view.format,
            MachineIntegerType::Int32 | MachineIntegerType::UInt32
        ) || view.relation != Relation::Equal
        {
            return None;
        }
        let pinned = |term: crate::kernel::MachineOperandView<'_>| {
            if solve_reasoning_interrupted() {
                return None;
            }
            if let Some(bits) = term.word32_constant() {
                Some((i64::from(bits as i32), None))
            } else {
                self.indexed_exact_int32_constant_view(term)
                    .map(|(value, source)| (value, Some(*source)))
            }
        };
        let (left_value, left_source) = pinned(view.operands[0].operand_view())?;
        let (right_value, right_source) = pinned(view.operands[1].operand_view())?;
        (left_value == right_value).then(|| left_source.into_iter().chain(right_source).collect())
    }

    pub(super) fn decide_algebraic_equality(
        &self,
        left: &AlgebraicTerm,
        right: &AlgebraicTerm,
    ) -> Option<bool> {
        if self.equality_graph.are_algebraic_equal(left, right) {
            return Some(true);
        }
        // Values known to be constructors of different variants differ.
        if let (Some(left), Some(right)) = (
            self.known_algebraic_constructor(left),
            self.known_algebraic_constructor(right),
        ) && let (
            AlgebraicTermNode::Constructor { variant: left, .. },
            AlgebraicTermNode::Constructor { variant: right, .. },
        ) = (&left.node, &right.node)
            && left != right
        {
            return Some(false);
        }
        self.exact_condition_value(&OldConditionTerm::AlgebraicEqual(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ))
    }
    pub(in crate::kernel) fn direct_bitvector_equality_evidence(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Option<DirectBitvectorEqualityEvidence> {
        self.direct_bitvector_equality_evidence_views(
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        )
    }

    pub(in crate::kernel) fn direct_bitvector_equality_evidence_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<DirectBitvectorEqualityEvidence> {
        if let Some(evidence) = self.direct_bitvector_equality_leaf_evidence(left, right) {
            return Some(evidence);
        }
        // Inspect native inputs directly. Retain endpoints only after a
        // cancellation succeeds, rather than importing every failed query.
        let mut current = shared_bitvector_equality_cancellation(left, right)?;
        let mut reductions = Vec::new();
        loop {
            reductions.push(current.clone());
            if let Some(mut evidence) = self.direct_bitvector_equality_leaf_evidence(
                current.0.operand_view(),
                current.1.operand_view(),
            ) {
                for (left, right) in reductions.into_iter().rev() {
                    evidence = DirectBitvectorEqualityEvidence::AdditiveCancellation {
                        left,
                        right,
                        equality: Box::new(evidence),
                    };
                }
                return Some(evidence);
            }
            let reduced = shared_bitvector_equality_cancellation(
                current.0.operand_view(),
                current.1.operand_view(),
            )?;
            if reduced == current {
                return None;
            }
            current = reduced;
        }
    }

    fn direct_bitvector_equality_leaf_evidence(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<DirectBitvectorEqualityEvidence> {
        if let Some(((left_value, left), (_right_value, right))) = self
            .signed_constant_evidence_view(left)
            .zip(self.signed_constant_evidence_view(right))
            .filter(|((left, _), (right, _))| left == right)
        {
            return Some(DirectBitvectorEqualityEvidence::EqualSignedConstants {
                value: left_value,
                left,
                right,
            });
        }
        let less_equal = Proposition::condition_is(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::LessEqual,
                [left, right],
            ),
            true,
        );
        let not_less_than = Proposition::condition_is(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::LessThan,
                [left, right],
            ),
            false,
        );
        if self.contains_assumed_exact(&less_equal) && self.contains_assumed_exact(&not_less_than) {
            return Some(DirectBitvectorEqualityEvidence::LeAndNotLt(Box::new(
                Int32LeAndNotLtEqualityEvidence {
                    less_equal,
                    not_less_than,
                },
            )));
        }
        let greater_equal = Proposition::condition_is(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::GreaterEqual,
                [left, right],
            ),
            true,
        );
        let not_greater_than = Proposition::condition_is(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::GreaterThan,
                [left, right],
            ),
            false,
        );
        (self.contains_assumed_exact(&greater_equal)
            && self.contains_assumed_exact(&not_greater_than))
        .then_some(DirectBitvectorEqualityEvidence::GeAndNotGt(Box::new(
            Int32GeAndNotGtEqualityEvidence {
                greater_equal,
                not_greater_than,
            },
        )))
    }

    fn indexed_exact_int32_constant(
        &self,
        term: &OldMachineTerm,
    ) -> Option<(i64, Box<Proposition>)> {
        self.indexed_exact_int32_constant_view(crate::kernel::MachineOperandView::Old(term))
    }

    pub(super) fn indexed_exact_int32_constant_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> Option<(i64, Box<Proposition>)> {
        let (condition, truth) = self.checked_scalar_facts.literal_equality(term)?;
        let source = Proposition::condition_is(condition.clone(), *truth);
        let value = SignedConstantEvidence::exact_equality_value_view(term, &source)?;
        Some((value, Box::new(source)))
    }

    fn signed_constant_evidence(
        &self,
        term: &OldMachineTerm,
    ) -> Option<(i64, SignedConstantEvidence)> {
        self.signed_constant_evidence_view(MachineOperandView::Old(term))
    }

    fn signed_constant_evidence_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<(i64, SignedConstantEvidence)> {
        if let Some(value) = term.word32_constant().map(|n| i64::from(n as i32)) {
            return Some((value, SignedConstantEvidence::Constant));
        }
        if let Some((value, source)) = self.indexed_exact_int32_constant_view(term) {
            return Some((value, SignedConstantEvidence::ExactEquality(source)));
        }
        let variable = *term.variable()?;
        let mut lower: Option<(i64, IndexedSignedOrderBoundEvidence)> = None;
        let mut upper: Option<(i64, IndexedSignedOrderBoundEvidence)> = None;
        for source in self
            .checked_order_bounds
            .constant_evidence_sources(&OldMachineTerm::Variable(variable))
            .into_iter()
            .flatten()
        {
            let Some((condition, value)) = source.old_condition() else {
                continue;
            };
            let view = order_view_at_format(condition, *value, MachineIntegerType::Int32)?;
            let strict = view.relation == crate::kernel::machine_integer::Relation::Less;
            let [left, right] = view
                .operands
                .each_ref()
                .map(|operand| operand.operand_view());
            let (other, forward) = if left.variable() == Some(&variable) {
                (right, true)
            } else if right.variable() == Some(&variable) {
                (left, false)
            } else {
                continue;
            };
            let pinned = self.indexed_exact_int32_constant_view(other);
            let other_value = other
                .word32_constant()
                .map(|bits| i64::from(bits as i32))
                .or_else(|| pinned.as_ref().map(|(value, _)| *value));
            let evidence = IndexedSignedOrderBoundEvidence {
                other_equality: pinned.map(|(_, source)| source),
                forward,
                source: Box::new(source),
            };
            if !forward
                && let Some(bound) = other_value
                && let Some(bound) = if strict {
                    bound.checked_add(1)
                } else {
                    Some(bound)
                }
                && lower.as_ref().is_none_or(|(current, _)| bound > *current)
            {
                lower = Some((bound, evidence.clone()));
            }
            if forward
                && let Some(bound) = other_value
                && let Some(bound) = if strict {
                    bound.checked_sub(1)
                } else {
                    Some(bound)
                }
                && upper.as_ref().is_none_or(|(current, _)| bound < *current)
            {
                upper = Some((bound, evidence));
            }
        }
        let ((lower_value, lower), (upper_value, upper)) = lower.zip(upper)?;
        (lower_value == upper_value).then_some((
            lower_value,
            SignedConstantEvidence::SingletonBounds {
                variable,
                lower,
                upper,
            },
        ))
    }

    pub(crate) fn singleton_constant_equality_evidence(
        &self,
        variable: Variable,
    ) -> Option<(i64, DirectBitvectorEqualityEvidence)> {
        let term = OldMachineTerm::Variable(variable);
        let (value, variable_evidence) = self.signed_constant_evidence(&term)?;
        Some((
            value,
            DirectBitvectorEqualityEvidence::EqualSignedConstants {
                value,
                left: variable_evidence,
                right: SignedConstantEvidence::Constant,
            },
        ))
    }

    /// Decides a condition against this fact set, memoizing results by the
    /// fact set's content identity.
    ///
    /// A `Some` answer is evidence found in the facts and stays valid no
    /// matter how the search was pruned. A `None` computed under an ambient
    /// interruption (verification limits or exact cycle cuts — see
    /// [`note_incomplete_reasoning`]) is path-dependent and is not cached.
    ///
    /// One outermost decision, with every decision nested in it, spends at
    /// most [`crate::instrumentation::DECISION_FUEL_LIMIT`] units; past that it ends undecided
    /// (`docs/internals/verification-efficiency.md`).
    pub(crate) fn decide(&self, condition: &OldConditionTerm) -> Option<bool> {
        let result = crate::instrumentation::with_decision_fuel(
            crate::instrumentation::DECISION_FUEL_LIMIT,
            || self.decide_unrecorded(condition),
        );
        if let Some(value) = result {
            record_implicit_consulted_premises(
                self,
                &Proposition::condition_is(condition.clone(), value),
            );
        }
        result
    }

    pub(super) fn decide_unrecorded(&self, condition: &OldConditionTerm) -> Option<bool> {
        if solve_reasoning_interrupted() {
            return None;
        }
        // The difference graph is read first: what it decides follows from
        // these facts, including a fact it showed implied and so was never
        // added (`docs/internals/verification-efficiency.md`). Only a graph already built
        // is read, so a context that withdrew a fact does not rebuild one.
        if let Some(value) = self
            .difference_graph
            .built()
            .and_then(|graph| graph.decide(condition))
        {
            return Some(value);
        }
        // Resolve the memo identity from an enclosing scope, or establish
        // one when this is the outermost decision. Nested decisions on other
        // fact sets (intrinsic decisions on fresh empty sets) run unmemoized.
        let scope = if inside_condition_decision() {
            None
        } else {
            Some(PureFactContextIdScope::enter(self))
        };
        let memo_id = scope
            .as_ref()
            .map(|scope| scope.id)
            .or_else(|| ambient_assumptions_memo_id(self));
        let Some(memo_id) = memo_id else {
            let _decision_guard = ConditionDecisionGuard::enter(condition)?;
            return self.decide_inner(condition);
        };
        let key = (memo_id, condition.clone());
        if let Some(hit) = DECIDE_MEMO.with(|memo| memo.borrow().get(&key).copied()) {
            return hit;
        }
        self.decide_uncached(&key, condition)
    }

    fn decide_uncached(
        &self,
        key: &(u64, OldConditionTerm),
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        let _decision_guard = ConditionDecisionGuard::enter(condition)?;
        let epoch_before = INCOMPLETE_REASONING_EPOCH.with(Cell::get);
        let result = self.decide_inner(condition);
        if result.is_some() || INCOMPLETE_REASONING_EPOCH.with(Cell::get) == epoch_before {
            DECIDE_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DECIDE_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(key.clone(), result);
            });
        }
        result
    }

    fn decide_inner(&self, condition: &OldConditionTerm) -> Option<bool> {
        // The read-over-write authority: a read of a stored cell is the
        // value stored there (`eval::read_over_write_value`). Consulted only
        // when the condition is undecided as written.
        self.decide_as_written(condition).or_else(|| {
            read_over_write_condition(condition)
                .and_then(|resolved| self.decide_as_written(&resolved))
        })
    }

    fn decide_as_written(&self, condition: &OldConditionTerm) -> Option<bool> {
        // A cited full pointer value equality also supplies the C address
        // comparison. Keep this projection indexed and positive only.
        if matches!(
            condition,
            OldConditionTerm::AddressEqual(..) | OldConditionTerm::AddressOffsetEqual(..)
        ) && (self
            .equality_graph
            .admitted
            .pointer_address_sources
            .contains_key(condition)
            || self
                .equality_graph
                .admitted
                .pointer_address_sources
                .contains_key(&condition.flipped()))
        {
            return Some(true);
        }
        if let OldConditionTerm::PointerEqual(left, right) = condition {
            if let Some(value) = self.exact_condition_value(condition) {
                return Some(value);
            }
            if self.equality_graph.knows_condition(condition, true) {
                return Some(true);
            }
            if self.equality_graph.knows_condition(condition, false) {
                return Some(false);
            }
            // Below, equal addresses decide the equality only for values
            // whose metadata is known equal, which the provenance match
            // includes (`pointer_metadata_known_equal`).
            if self.pointer_provenance_match(left, right)
                && (crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                    left.address(),
                    right.address(),
                    self,
                ) || crate::kernel::memory_history::pointer_read_has_recorded_value(
                    left.address(),
                    right.address(),
                    self,
                ))
            {
                return Some(true);
            }
            let address = self.decide(&OldConditionTerm::address_equal(
                left.address().clone(),
                right.address().clone(),
            ));
            return match address {
                Some(false) => Some(false),
                Some(true) if self.pointer_provenance_match(left, right) => Some(true),
                _ => None,
            };
        }
        // A comparison of a term with itself is decided by its shape, with
        // no fact: the same one-comparison rule every `using` list applies
        // (`proposition_holds_without_facts`).
        if let Some(value) = condition
            .reflexive_value()
            .or_else(|| condition.literal_float_comparison_value())
        {
            return Some(value);
        }
        // A `Bool` binder that an L-Eq merge gave a truth. A binder no
        // `Bool` value names has no class and is decided as before.
        if let OldConditionTerm::Variable(_) = condition {
            for value in [true, false] {
                if self.equality_graph.knows_condition(condition, value) {
                    return Some(value);
                }
            }
            if let Some(value) = self.decide_by_bool_equation_partners(condition) {
                return Some(value);
            }
        }
        if condition.is_bool_value_form() {
            return self.decide_bool_value(condition);
        }
        // Ordinary arithmetic range bounds can use the same bounded interval
        // calculation as execution. A nonoverflow result proves each bound;
        // an overflow result alone does not select which bound failed.
        if let Some(query) =
            crate::kernel::machine_integer::definedness::overflow_query_of_integer_bound(
                &Proposition::condition_is(condition.clone(), true),
                crate::kernel::machine_integer::definedness::defined_formats(),
            )
            && self.decide_overflow_query(&query) == Some(false)
        {
            return Some(true);
        }
        // These range rules read the original comparison's operand views.
        // Dispatch them before the native compatibility conversion so shared
        // arithmetic does not need a boxed tree to answer a range query.
        if let Some(value) = self.decide_masked_order(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_widened_sum_bound(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_indexed_greater_equal(condition) {
            return Some(value);
        }
        if let Some(value) =
            super::super::observation_comparisons::constant_observation_value(condition)
        {
            return Some(value);
        }
        // Read native comparison classes through shared observations before
        // the remaining arithmetic decision rules cross the boxed boundary.
        if crate::kernel::machine_integer::comparison::native_comparison_view(condition, true)
            .is_some()
            && let Some(value) = self.known_condition_value(condition)
        {
            return Some(value);
        }
        if let Some(value) = self.decide_signed_constant_offset_order(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_shared_conditional_comparison(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_shared_signed_constant_order(condition) {
            return Some(value);
        }
        // Equality of the operands settles order before an interval walk.
        // Other reductions retain the legacy simplifier's later rule position.
        if let Some(value) = self
            .shared_word_checking_form(condition)
            .and_then(|read| read.reflexive_value())
        {
            return Some(value);
        }
        // The compatibility decision consulted an already-built graph here,
        // after the cheap observation rules and before the native order rules.
        if !matches!(condition, OldConditionTerm::Compare { .. })
            && let Some(view) =
                crate::kernel::machine_integer::comparison::native_comparison_view(condition, true)
            && let Some(value) = self
                .difference_graph
                .built()
                .and_then(|graph| graph.decide_shared_order(&view))
        {
            return Some(value);
        }
        let checked_shared_word_order = !matches!(condition, OldConditionTerm::Compare { .. })
            && crate::kernel::machine_integer::comparison::native_comparison_view(condition, true)
                .is_some_and(|view| {
                    matches!(
                        view.format,
                        MachineIntegerType::Int32 | MachineIntegerType::UInt32
                    )
                });
        if checked_shared_word_order && let Some(value) = self.decide_from_order_facts(condition) {
            return Some(value);
        }
        // Retained comparison rules keep their compatibility dispatch order:
        // narrow widening, wide/index bounds, then signedness readings.
        if !matches!(condition, OldConditionTerm::Compare { .. }) {
            if let Some(view) =
                crate::kernel::machine_integer::comparison::structural_native_comparison_view(
                    condition, true,
                )
                && let Some(widened) = view.widened()
                && let Some(value) = self.decide(&widened.integer_condition())
            {
                return Some(value);
            }
            if let Some(value) = self.decide_uint64_constant_order_bounds(condition) {
                return Some(value);
            }
            if let Some(value) = self.decide_small_uint64_index_order(condition) {
                return Some(value);
            }
            if let Some(value) = self.decide_wide_order_chain(condition) {
                return Some(value);
            }
            if let Some(value) = self.decide_unsigned_order_of_nonnegative_signed(condition) {
                return Some(value);
            }
            if let Some(value) = self.decide_by_sign_bit(condition) {
                return Some(value);
            }
            if let Some(value) = self.decide_by_sign_cast_division(condition) {
                return Some(value);
            }
        }
        // The mask rule retains its selected bound and operand structure.
        if let Some(value) = self.decide_shared_mask_zero(condition, &mut Default::default()) {
            return Some(value);
        }
        // Wide tagged-address reasoning reads the original retained operands.
        if let Some(view) =
            crate::kernel::machine_integer::comparison::native_comparison_view(condition, true)
            && view.format.format().bits() == 64
            && matches!(
                view.relation,
                crate::kernel::machine_integer::Relation::Equal
                    | crate::kernel::machine_integer::Relation::NotEqual
            )
            && let Some(value) = self.decide_uint64_equality_extras_views(
                view.operands[0].operand_view(),
                view.operands[1].operand_view(),
                &mut Default::default(),
            )
        {
            return Some(
                value == (view.relation == crate::kernel::machine_integer::Relation::Equal),
            );
        }
        // Fixed-size atoms and already-native operands can still use their
        // native comparison rules. Shared arithmetic is never exported here.
        if let Some(view) =
            crate::kernel::machine_integer::comparison::native_comparison_view(condition, true)
            && !matches!(
                view.format,
                MachineIntegerType::Int32 | MachineIntegerType::UInt32
            )
            && !matches!(
                view.relation,
                crate::kernel::machine_integer::Relation::Less
                    | crate::kernel::machine_integer::Relation::LessEqual
            )
            && let (native, truth) = view.retained_condition()
            && matches!(
                native,
                OldConditionTerm::Compare { .. } | OldConditionTerm::Constant(_)
            )
            && &native != condition
            && let Some(value) = self.decide(&native)
        {
            return Some(value == truth);
        }
        // A native 8- or 16-bit comparison has the truth of the signed
        // `int32` comparison of its operands' widenings, which the 32-bit
        // reasoning below decides (`narrow_comparison_as_int32`).
        if let Some(widened) =
            crate::kernel::machine_integer::comparison::narrow_comparison_as_int32(condition)
            && let Some(value) = self.decide(&widened)
        {
            return Some(value);
        }
        if let Some(value) = self.decide_uint64_constant_order_bounds(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_small_uint64_index_order(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_wide_order_chain(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_unsigned_order_of_nonnegative_signed(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_by_sign_bit(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_by_sign_cast_division(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_wide_constant_comparison(condition) {
            return Some(value);
        }
        match condition {
            OldConditionTerm::AlgebraicEqual(left, right) => {
                self.decide_algebraic_equality(left, right)
            }
            OldConditionTerm::Constant(value) => Some(*value),
            _ => {
                if let Some(value) = self.known_condition_value(condition) {
                    return Some(value);
                }
                if let Some(value) = self.decide_exact_signed_constant_order(condition) {
                    return Some(value);
                }
                if let Some(value) = self.decide_exact_unsigned32_constant_order(condition) {
                    return Some(value);
                }
                if let Some(value) = self.decide_byte_equality_from_constant_class(condition) {
                    return Some(value);
                }
                if let Some(value) = self.decide_reflexive_float_comparison(condition) {
                    return Some(value);
                }
                if let OldConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, left, right } = condition
                    && (self.int32_values_known_equal(left, right)
                        || super::super::super::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                            left,
                            right,
                            self,
                        ))
                {
                    return Some(true);
                }
                if let OldConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                } = condition
                    && crate::kernel::memory_history::wide_loads_have_same_canonical_value(
                        left, right, self,
                    )
                {
                    return Some(true);
                }
                if let OldConditionTerm::AddressEqual(left, right) = condition
                    && (crate::kernel::memory_history::pointer_read_has_stored_value(
                        left, right, self,
                    ) || crate::kernel::memory_history::pointer_read_has_stored_value(
                        right, left, self,
                    ))
                {
                    return Some(true);
                }
                // The Integer carrier's counterpart of the fold congruence
                // the int32 equality above reaches through
                // `range_fold_terms_alpha_equivalent`: two range folds with
                // the same initial value and body are equal when their
                // endpoints are. The helper matches two `RangeFold` nodes
                // before it consults anything, so every other Integer
                // equality pays one enum test.
                if let OldConditionTerm::IntegerEqual(left, right) = condition
                    && super::super::super::reasoning::integer_range_fold_terms_alpha_equivalent(
                        left, right, self,
                    )
                {
                    return Some(true);
                }
                // Pointer conditions are already in their canonical structural
                // form: `simplify_condition_under_assumptions` only clones
                // them. Avoid cloning and then deeply comparing symbolic
                // pointer terms (which may embed whole memory states)
                // before routing to the dedicated pointer decision rules.
                if matches!(
                    condition,
                    OldConditionTerm::AddressOffsetEqual(_, _)
                        | OldConditionTerm::AddressEqual(_, _)
                ) {
                    return self
                        .condition_facts
                        .get(condition)
                        .copied()
                        .or_else(|| self.decide_pointer_disequality(condition))
                        .or_else(|| self.decide_from_order_facts(condition));
                }
                let simplified = self.simplify_condition_under_assumptions(condition);
                if simplified != *condition {
                    if let Some(value) = simplified.reflexive_value() {
                        return Some(value);
                    }
                    return match simplified {
                        OldConditionTerm::Constant(value) => Some(value),
                        simplified => self
                            .condition_facts
                            .get(condition)
                            .copied()
                            .or_else(|| self.condition_facts.get(&simplified).copied())
                            .or_else(|| self.decide_from_overflow_facts(&simplified))
                            .or_else(|| self.decide_from_order_facts(&simplified)),
                    };
                }

                self.condition_facts
                    .get(condition)
                    .copied()
                    .or_else(|| self.decide_from_overflow_facts(condition))
                    // The retained word query above already checked these
                    // facts. Only a changed simplification needs another
                    // order query (handled in the branch above).
                    .or_else(|| {
                        if checked_shared_word_order {
                            None
                        } else {
                            self.decide_from_order_facts(condition)
                        }
                    })
            }
        }
    }

    /// Decides a pointer comparison false from what the context already
    /// states about the two pointers themselves: that one is null and the
    /// other is not, or that each holds the first element of one of two
    /// separated memory ranges.
    ///
    /// Both routes are keyed lookups on the pointers in the query, never a
    /// search: null-ness is indexed by the offset term a null test named,
    /// and separation by the pair of anchor offsets. Neither ever answers
    /// `Some(true)`; two pointers may be equal for reasons no index holds.
    pub(in crate::kernel) fn decide_pointer_disequality(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        if self.addresses_separated_by_class(condition) {
            return Some(false);
        }
        match condition {
            OldConditionTerm::AddressEqual(left, right) => self
                .pointers_distinct_by_nullness(left, right)
                .or_else(|| self.pointers_distinct_by_stated_separation(left, right)),
            OldConditionTerm::AddressOffsetEqual(left, right) => self
                .offsets_distinct_by_nullness(left, right)
                .or_else(|| self.offsets_distinct_by_stated_separation(left, right)),
            _ => None,
        }
    }

    /// The explicitly stated separation consequence shared by C conditions
    /// and proof-side known-fact lookup. It only reads the selected anchor
    /// index and records the exact separation premise; it never searches
    /// owned compositions or resolves aliases.
    pub(in crate::kernel) fn stated_pointer_disequality(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        match condition {
            OldConditionTerm::AddressEqual(left, right) => {
                self.pointers_distinct_by_stated_separation(left, right)
            }
            OldConditionTerm::AddressOffsetEqual(left, right) => {
                self.offsets_distinct_by_stated_separation(left, right)
            }
            _ => None,
        }
    }

    /// Explicit separation uses exactly the comparison's two anchors. Do not
    /// route a missing pointer query through the offset consumer's legacy
    /// composition scan: unrelated ownership is not a candidate for this index.
    fn pointers_distinct_by_stated_separation(
        &self,
        left: &Address,
        right: &Address,
    ) -> Option<bool> {
        if left == right {
            return None;
        }
        if left.base == right.base {
            return self.offsets_distinct_by_stated_separation(&left.offset, &right.offset);
        }
        let key = Self::separated_pointer_key(left.clone(), right.clone());
        let separation = self.separated_anchor_pointers.get(&key)?.iter().next()?;
        record_implicit_consulted_premises(self, separation);
        Some(false)
    }

    fn offsets_distinct_by_stated_separation(
        &self,
        left: &AddressOffset,
        right: &AddressOffset,
    ) -> Option<bool> {
        if left == right {
            return None;
        }
        let key = Self::separated_anchor_key(left.clone(), right.clone());
        let separation = self.separated_anchor_offsets.get(&key)?.iter().next()?;
        record_implicit_consulted_premises(self, separation);
        Some(false)
    }

    fn pointers_distinct_by_nullness(&self, left: &Address, right: &Address) -> Option<bool> {
        let left = self.pointer_nullness(left)?;
        let right = self.pointer_nullness(right)?;
        (left != right).then_some(false)
    }

    /// The spellings exact equalities give one pointer: itself and every
    /// pointer the alias indexes connect it to, through block aliases and
    /// same-block offset aliases alike. Each spelling is paired with the
    /// spelling it was reached from, so the equalities a conclusion rests
    /// on can be taken back through the exact check. Evidence-producing
    /// consumers retain this output-sensitive enumeration; Boolean equality
    /// queries use `pointers_known_equal` instead. Each adjacency is keyed,
    /// and the walk visits only the component reachable from `start`.
    pub(in crate::kernel) fn pointer_equality_component(
        &self,
        start: &Address,
    ) -> Vec<(Address, Option<Address>)> {
        let mut seen = std::collections::BTreeSet::from([start.clone()]);
        let mut reached = vec![(start.clone(), None)];
        let mut frontier = vec![start.clone()];
        while let Some(current) = frontier.pop() {
            let aliases = self
                .exact_pointer_aliases(&current)
                .cloned()
                .chain(self.exact_pointer_offset_aliases(&current))
                .collect::<Vec<_>>();
            for alias in aliases {
                crate::instrumentation::record_deterministic_work(1);
                if seen.insert(alias.clone()) {
                    reached.push((alias.clone(), Some(current.clone())));
                    frontier.push(alias);
                }
            }
        }
        reached
    }

    /// Whether an exact fact settles this pointer's null-ness.
    ///
    /// The null pointer is null intrinsically, and a pointer whose block is
    /// proven distinct from the null block is not null by the same rule that
    /// decides any other block disequality.
    fn pointer_nullness(&self, pointer: &Address) -> Option<bool> {
        let null = Address::null();
        if *pointer == null {
            return Some(true);
        }
        if let Some(value) = self.exact_condition_value(&OldConditionTerm::AddressEqual(
            Box::new(pointer.clone()),
            Box::new(null.clone()),
        )) {
            return Some(value);
        }
        pointer.blocks_proven_distinct(&null).then_some(false)
    }

    /// Two offsets differ when one names a null pointer of some block and
    /// the other names a non-null pointer of that same block: if the offsets
    /// were equal the two pointers would be one pointer.
    fn offsets_distinct_by_nullness(
        &self,
        left: &AddressOffset,
        right: &AddressOffset,
    ) -> Option<bool> {
        let left_blocks = self.null_pointer_offsets.get(left)?;
        let right_blocks = self.null_pointer_offsets.get(right)?;
        // One entry per block a null test named for this exact offset term,
        // which in practice is the single block the pointer came from.
        for ((block, value), _) in left_blocks.iter() {
            if !right_blocks.contains_key(&(block.clone(), !*value)) {
                continue;
            }
            // The index only nominates the block. Both premises are then
            // taken through the exact check, so they are recorded exactly
            // and a stale entry can never decide anything on its own.
            let pointer_at = |offset: &AddressOffset| Address::new(block.clone(), offset.clone());
            if self.pointer_nullness(&pointer_at(left)) == Some(*value)
                && self.pointer_nullness(&pointer_at(right)) == Some(!*value)
            {
                return Some(false);
            }
        }
        None
    }

    fn decide_reflexive_float_comparison(&self, condition: &OldConditionTerm) -> Option<bool> {
        let (operator, left, right) = match condition {
            OldConditionTerm::Float32(FloatCondition::Comparison {
                operator,
                left,
                right,
            }) => (*operator, left.as_ref(), right.as_ref()),
            OldConditionTerm::Float64(FloatCondition::Comparison {
                operator,
                left,
                right,
            }) => (*operator, left.as_ref(), right.as_ref()),
            _ => return None,
        };
        if left != right
            && !super::super::super::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                left, right, self,
            )
        {
            return None;
        }
        let finite_left = match condition {
            OldConditionTerm::Float32(_) => {
                OldConditionTerm::float32_classification(left.clone(), FloatClassification::Finite)
            }
            OldConditionTerm::Float64(_) => {
                OldConditionTerm::float64_classification(left.clone(), FloatClassification::Finite)
            }
            _ => unreachable!(),
        };
        let finite_right = match condition {
            OldConditionTerm::Float32(_) => {
                OldConditionTerm::float32_classification(right.clone(), FloatClassification::Finite)
            }
            OldConditionTerm::Float64(_) => {
                OldConditionTerm::float64_classification(right.clone(), FloatClassification::Finite)
            }
            _ => unreachable!(),
        };
        let left_is_finite = self.decide(&finite_left);
        let right_is_finite = self.decide(&finite_right);
        if left_is_finite != Some(true) && right_is_finite != Some(true) {
            return None;
        }
        Some(match operator {
            ComparisonOperator::Equal
            | ComparisonOperator::LessEqual
            | ComparisonOperator::GreaterEqual => true,
            ComparisonOperator::NotEqual
            | ComparisonOperator::LessThan
            | ComparisonOperator::GreaterThan => false,
        })
    }

    /// Decide a `Bool` value that is not a comparison
    /// (`design/machine-integers.md`, Stage 5): by its own fact, by its
    /// class in the e-graph (rule L-Eq), or by its parts.
    ///
    /// A conditional is opened here, on demand (rule L-If): a decided
    /// condition selects its branch, and branches decided alike decide it
    /// whatever the condition. An equality is decided by its decided
    /// operands. Each part is decided once, through the memo, so the work
    /// is the value's size; nothing is filed.
    fn decide_bool_value(&self, condition: &OldConditionTerm) -> Option<bool> {
        if let Some(value) = self.exact_condition_value(condition) {
            return Some(value);
        }
        for value in [true, false] {
            if self.equality_graph.knows_condition(condition, value) {
                return Some(value);
            }
        }
        let decide = |operand: &OldConditionTerm| match operand {
            OldConditionTerm::Constant(value) => Some(*value),
            operand => self.decide(operand),
        };
        match condition {
            OldConditionTerm::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => match decide(condition) {
                Some(true) => decide(then_condition),
                Some(false) => decide(else_condition),
                None => {
                    let then_value = decide(then_condition)?;
                    (decide(else_condition)? == then_value).then_some(then_value)
                }
            },
            OldConditionTerm::BoolEqual(left, right) => Some(decide(left)? == decide(right)?),
            _ => None,
        }
        .or_else(|| self.decide_by_bool_equation_partners(condition))
    }

    /// Rule L-Eq read through a `Bool` equality fact: when `a == b` has
    /// truth `t` and `b` is decided, `a` is `b`'s truth if `t` and its
    /// negation otherwise. One lookup of the operand's partners.
    fn decide_by_bool_equation_partners(&self, condition: &OldConditionTerm) -> Option<bool> {
        let partners = self.bool_equation_partners.get(condition)?;
        partners.iter().find_map(|(partner, equal)| {
            let truth = match partner {
                OldConditionTerm::Constant(value) => *value,
                partner => self.decide(partner)?,
            };
            Some(truth == *equal)
        })
    }

    pub(in crate::kernel) fn decide_intrinsically(condition: &OldConditionTerm) -> Option<bool> {
        // Drop the thread-local borrow before deciding: compound guards can
        // ask another intrinsic question recursively.
        let context = INTRINSIC_CONTEXT.with(|slot| {
            slot.borrow_mut()
                .get_or_insert_with(|| std::rc::Rc::new(Self::new()))
                .clone()
        });
        context.decide(condition)
    }

    /// A byte read compared with a constant, decided by the constant its
    /// shared equality class carries. One byte has one name, so
    /// its signed and unsigned reads share that class's evidence in both
    /// directions: `int8(u) == 7` settles `u` to 7 and `u == 200` settles
    /// `int8(u)` to -56 (see `equality_graph::terms::constants`). The queried side must be a
    /// byte read, an unsigned byte load or the signed conversion of one, so
    /// this answers only the byte questions the index was extended for; it
    /// is one memoized class lookup, not a walk over the facts.
    fn decide_byte_equality_from_constant_class(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        let OldConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
        else {
            return None;
        };
        let (term, constant) = match (
            signed_bitvector_constant(left),
            signed_bitvector_constant(right),
        ) {
            (None, Some(constant)) => (left.as_ref(), constant),
            (Some(constant), None) => (right.as_ref(), constant),
            _ => return None,
        };
        let byte = term.signed_byte_operand().unwrap_or(term);
        if !matches!(
            crate::kernel::eval::viewed_as_memory_load(byte),
            Some(OldMachineTerm::MemoryLoad(_, _, LoadKind::UInt8))
        ) {
            return None;
        }
        self.signed_constant_after_equality_normalization(term)
            .map(|known| known == constant)
    }

    /// Decide a signed byte comparison from the exact equality bucket of
    /// its unsigned read. Frozen execution cites that original equality;
    /// exact membership and arbitrary cast operands remain unchanged.
    pub(in crate::kernel) fn decide_signed_byte_equality_from_exact_fact(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        let OldConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
        else {
            return None;
        };
        let (byte, target) = if let Some(byte) = left.signed_byte_operand() {
            (byte, right.as_ref())
        } else {
            (right.signed_byte_operand()?, left.as_ref())
        };
        if !matches!(
            crate::kernel::eval::viewed_as_memory_load(byte),
            Some(OldMachineTerm::MemoryLoad(_, _, LoadKind::UInt8))
        ) {
            return None;
        }
        let target = signed_bitvector_constant(target)?;
        let (unsigned, source) = self.indexed_exact_int32_constant(byte)?;
        let unsigned = u8::try_from(unsigned).ok()?;
        let signed = OldMachineTerm::signed_byte(OldMachineTerm::constant(u32::from(unsigned)))
            .as_const()? as i32;
        record_implicit_consulted_premises(self, &source);
        Some(i64::from(signed) == target)
    }

    /// Integer strict and inclusive bounds differ by one. Keep the frozen
    /// bounded term intact and look up only the equivalent recorded bound.
    /// The signed endpoints are handled before incrementing or decrementing.
    pub(super) fn decide_exact_signed_constant_order(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        self.decide_exact_word_constant_order(condition, MachineIntegerType::Int32)
    }

    /// The same adjacent-bound rule at the unsigned word's endpoints.
    pub(super) fn decide_exact_unsigned32_constant_order(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        self.decide_exact_word_constant_order(condition, MachineIntegerType::UInt32)
    }

    fn decide_exact_word_constant_order(
        &self,
        condition: &OldConditionTerm,
        format: MachineIntegerType,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::{
            Relation,
            comparison::{comparison_view, condition_for_operand_views},
        };
        // The shared constructor can settle an endpoint from the operand's
        // intrinsic unsigned range before this adjacent-bound query runs.
        if let OldConditionTerm::Constant(value) = condition {
            return Some(*value);
        }
        let view = comparison_view(condition, true)?;
        if view.format != format {
            return None;
        }
        let strict = match view.relation {
            Relation::Less => true,
            Relation::LessEqual => false,
            _ => return None,
        };
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let (term, bits, greater) = if let Some(bound) = right.word32_constant() {
            (left, bound, false)
        } else {
            (right, left.word32_constant()?, true)
        };
        let (bound, minimum, maximum) = if format == MachineIntegerType::Int32 {
            (
                i64::from(bits as i32),
                i64::from(i32::MIN),
                i64::from(i32::MAX),
            )
        } else {
            (i64::from(bits), 0, i64::from(u32::MAX))
        };
        let shifted = bound + if greater == strict { 1 } else { -1 };
        if shifted < minimum || shifted > maximum {
            return Some(!strict);
        }
        let bound = OldMachineTerm::constant(shifted as u32);
        let relation = match (greater, strict) {
            (true, true) => CompareRelation::GreaterEqual,
            (true, false) => CompareRelation::GreaterThan,
            (false, true) => CompareRelation::LessEqual,
            (false, false) => CompareRelation::LessThan,
        };
        self.decide_by_equivalent_order(&condition_for_operand_views(
            format,
            relation,
            [term, MachineOperandView::Old(&bound)],
        ))
    }

    /// The exact fact of `equivalent`, an order equivalent to the one asked,
    /// directly or through an indexed spelling of its sides.
    fn decide_by_equivalent_order(&self, equivalent: &OldConditionTerm) -> Option<bool> {
        self.known_condition_value(equivalent)
    }

    pub(in crate::kernel) fn has_condition_fact(
        &self,
        condition: OldConditionTerm,
        value: bool,
    ) -> bool {
        if let Some(known) = self.exact_condition_value(&condition) {
            return known == value;
        }
        if self.equality_graph.knows_condition(&condition, value) {
            record_implicit_consulted_premises(self, &Proposition::condition_is(condition, value));
            return true;
        }
        // Exact canonical shape, then at most one source per explicitly
        // mentioned variable. Neither equality classes nor crowded buckets
        // are implicit premise lists.
        let matched = crate::kernel::assumptions::condition_match_key(&condition)
            .and_then(|key| self.condition_facts_by_sides.get(&key))
            .filter(|facts| facts.len() == 1)
            .and_then(|facts| facts.iter().next())
            .filter(|(fact, fact_value)| {
                crate::instrumentation::record_deterministic_work(1);
                **fact_value == value && self.condition_matches(fact, &condition)
            })
            .map(|(fact, fact_value)| Proposition::condition_is(fact.clone(), *fact_value))
            .or_else(|| {
                let mut variables = BTreeSet::new();
                let _ = crate::kernel::reasoning::variable_collection::collect_condition_index_variables(
                    &condition, &mut variables,
                );
                variables.iter().find_map(|variable| {
                    crate::instrumentation::record_deterministic_work(1);
                    let (fact, fact_value) = self.singleton_condition_variable(*variable)?;
                    (fact_value == value && self.condition_matches(fact, &condition))
                        .then(|| Proposition::condition_is(fact.clone(), fact_value))
                })
            });
        if let Some(proposition) = matched {
            record_implicit_consulted_premises(self, &proposition);
            true
        } else {
            false
        }
    }

    /// The same scoped fact through the shared condition application index.
    /// Address-origin annotations do not alter a numeric condition's truth.
    pub(in crate::kernel) fn known_condition_value(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        self.exact_condition_value(condition).or_else(|| {
            let value = [true, false]
                .into_iter()
                .find(|value| self.equality_graph.knows_condition(condition, *value))?;
            record_implicit_consulted_premises(
                self,
                &Proposition::condition_is(condition.clone(), value),
            );
            Some(value)
        })
    }

    /// The exact recorded value of `condition` (or of its mirrored form),
    /// recording the fact as a consulted premise when a collection is
    /// active: an exact lookup is a premise like any other.
    pub(in crate::kernel) fn exact_condition_value(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        if let OldConditionTerm::Constant(literal) = condition {
            return self.exact_literal_value(*literal);
        }
        if let OldConditionTerm::Overflows {
            format,
            op,
            left,
            right,
        } = condition
        {
            return self.exact_overflow_value(*format, *op, left, right);
        }
        if self.condition_facts.get(condition).is_none() {
            for truth in [true, false] {
                if let Some(source) = self.observation_comparisons.source(condition, truth) {
                    record_implicit_consulted_premises(self, source);
                    return Some(truth);
                }
            }
        }
        let value = self.exact_condition_value_unrecorded(condition);
        if let Some(value) = value {
            record_implicit_consulted_premises(
                self,
                &Proposition::condition_is(condition.clone(), value),
            );
        }
        value
    }

    fn exact_literal_value(&self, literal: bool) -> Option<bool> {
        if let Some(value) = self.condition_facts.literal_value(literal) {
            if implicit_consulted_premises_capturing() {
                let fact = Proposition::ConditionIs(
                    crate::kernel::StoredConditionTerm::constant(literal),
                    value,
                );
                record_implicit_consulted_premises(self, &fact);
            }
            return Some(value);
        }
        for truth in [true, false] {
            if let Some(source) = self.observation_comparisons.literal_source(literal, truth) {
                record_implicit_consulted_premises(self, source);
                return Some(truth);
            }
        }
        None
    }

    /// Use the literal condition's exact lookup when both signed words fold.
    /// A symbolic sum is looked up with its written operand ordering.
    pub(in crate::kernel) fn exact_signed_add_overflow(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Option<bool> {
        let words = [left, right].map(OldMachineTerm::constant32);
        if let [Some(a), Some(b)] = words {
            return self.exact_literal_value((a as i32).overflowing_add(b as i32).1);
        }
        let literals = words.map(|word| word.map(OldMachineTerm::constant));
        self.exact_overflow_value(
            MachineIntegerType::Int32,
            OverflowOperation::Add,
            literals[0].as_ref().unwrap_or(left),
            literals[1].as_ref().unwrap_or(right),
        )
    }

    fn exact_overflow_value(
        &self,
        format: MachineIntegerType,
        op: OverflowOperation,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::{Operation, definedness, representation};
        let direct = self
            .condition_facts
            .written_overflow_value(format, op, left, right);
        let bounds = Operation::from_overflow(op)
            .filter(|_| representation::has_overflow_test(format))
            .and_then(|operation| {
                definedness::bounds_for_operation(
                    format,
                    operation,
                    [left, right].map(MachineOperandView::Old),
                )
            });
        let from_bounds = bounds.as_ref().is_some_and(|bounds| {
            bounds.iter().all(|bound| {
                let Proposition::ConditionIs(condition, true) = bound else {
                    return false;
                };
                Self::decide_intrinsically(condition.old_form()) == Some(true)
                    || integer_order_spellings(condition.old_form())
                        .into_iter()
                        .any(|condition| {
                            self.contains_known(&Proposition::condition_is(condition, true))
                        })
            })
        });
        let value = if from_bounds { false } else { direct? };
        if implicit_consulted_premises_capturing() {
            if direct.is_some() {
                let written = crate::kernel::StoredConditionTerm::written_overflow(
                    format,
                    op,
                    [left, right].map(crate::kernel::MachineOperandView::Old),
                );
                record_implicit_consulted_premises(self, &Proposition::ConditionIs(written, value));
            } else if let Some(bounds) = bounds {
                for bound in bounds {
                    record_implicit_consulted_premises(self, &bound);
                }
            }
        }
        Some(value)
    }

    fn exact_condition_value_unrecorded(&self, condition: &OldConditionTerm) -> Option<bool> {
        self.condition_facts
            .get(condition)
            .copied()
            .or_else(|| match condition {
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                } => self
                    .condition_facts
                    .get(&OldConditionTerm::equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied(),
                condition
                    if let Some(pair) =
                        crate::kernel::WrittenPointerEquality::from_condition(condition) =>
                {
                    pair.reversed_exact_value(&self.condition_facts)
                }
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left,
                    right,
                } => self
                    .condition_facts
                    .get(&OldConditionTerm::signed_greater_than(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied()
                    .or_else(|| {
                        self.condition_facts
                            .get(&OldConditionTerm::signed_greater_equal(
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                            ))
                            .map(|value| !value)
                    }),
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left,
                    right,
                } => self
                    .condition_facts
                    .get(&OldConditionTerm::signed_greater_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied()
                    .or_else(|| {
                        self.condition_facts
                            .get(&OldConditionTerm::signed_greater_than(
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                            ))
                            .map(|value| !value)
                    }),
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left,
                    right,
                } => self
                    .condition_facts
                    .get(&OldConditionTerm::signed_less_than(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied()
                    .or_else(|| {
                        self.condition_facts
                            .get(&OldConditionTerm::signed_less_equal(
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                            ))
                            .map(|value| !value)
                    }),
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left,
                    right,
                } => self
                    .condition_facts
                    .get(&OldConditionTerm::signed_less_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied()
                    .or_else(|| {
                        self.condition_facts
                            .get(&OldConditionTerm::signed_less_than(
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                            ))
                            .map(|value| !value)
                    }),
                // A `uint32` order's mirrored spelling, and its converse.
                OldConditionTerm::Compare {
                    format: MachineIntegerType::UInt32,
                    relation:
                        relation @ (crate::kernel::CompareRelation::LessThan
                        | crate::kernel::CompareRelation::LessEqual
                        | crate::kernel::CompareRelation::GreaterThan
                        | crate::kernel::CompareRelation::GreaterEqual),
                    left,
                    right,
                } => {
                    let spelled = |relation: CompareRelation,
                                   left: &OldMachineTerm,
                                   right: &OldMachineTerm| {
                        self.condition_facts.get(&OldConditionTerm::Compare {
                            format: MachineIntegerType::UInt32,
                            relation,
                            left: Box::new(left.clone()),
                            right: Box::new(right.clone()),
                        })
                    };
                    let (mirrored, converse) = match relation {
                        CompareRelation::LessThan => {
                            (CompareRelation::GreaterThan, CompareRelation::GreaterEqual)
                        }
                        CompareRelation::LessEqual => {
                            (CompareRelation::GreaterEqual, CompareRelation::GreaterThan)
                        }
                        CompareRelation::GreaterThan => {
                            (CompareRelation::LessThan, CompareRelation::LessEqual)
                        }
                        CompareRelation::GreaterEqual => {
                            (CompareRelation::LessEqual, CompareRelation::LessThan)
                        }
                        CompareRelation::Equal => return None,
                    };
                    spelled(mirrored, right, left)
                        .copied()
                        .or_else(|| spelled(converse, left, right).map(|value| !value))
                }
                _ => None,
            })
    }

    #[cfg(test)]
    pub(in crate::kernel) fn decide_bitvector_equality_shallow(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Option<bool> {
        self.decide_bitvector_equality_shallow_views(
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        )
    }

    pub(in crate::kernel) fn decide_bitvector_equality_shallow_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<bool> {
        if self.equality_graph.are_int32_equal_views(left, right) {
            return Some(true);
        }
        if let Some(value) = self.exact_int32_equality_value_views(left, right) {
            return Some(value);
        }
        // Purely structural arithmetic: terms whose affine difference is a
        // constant that is nonzero mod 2^32 are unequal in every model
        // (x + c wraps back to x only when c is a multiple of 2^32). No
        // facts are consulted, so the verdict is identical in smart
        // execution and pinned check.
        if let Some(difference) = affine_bitvector_difference_constant_views(left, right)
            && difference.rem_euclid(1i64 << 32) != 0
        {
            return Some(false);
        }
        match (
            self.equality_graph.direct_scalar_constant_view(left),
            self.equality_graph.direct_scalar_constant_view(right),
        ) {
            (Some(left), Some(right)) => Some(left == right),
            _ => None,
        }
    }

    pub(in crate::kernel) fn bitvector_constant_from_direct_equalities(
        &self,
        term: &OldMachineTerm,
    ) -> Option<u32> {
        self.equality_graph.direct_scalar_constant(term)
    }

    /// Preserve the existing wide constant rules on borrowed operand roots.
    fn decide_wide_constant_comparison(&self, condition: &OldConditionTerm) -> Option<bool> {
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let view = comparison_view(condition, true)?;
        if !matches!(
            view.format,
            MachineIntegerType::Int64 | MachineIntegerType::UInt64
        ) {
            return None;
        }
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let equality = matches!(view.relation, Relation::Equal | Relation::NotEqual);
        let negate = view.relation == Relation::NotEqual;
        if equality {
            let a = self.bitvector64_identity_base_view(left);
            let b = self.bitvector64_identity_base_view(right);
            let same_root = |a, b| match (a, b) {
                (MachineOperandView::Old(a), MachineOperandView::Old(b)) => std::ptr::eq(a, b),
                (MachineOperandView::Shared(a), MachineOperandView::Shared(b)) => a == b,
                _ => false,
            };
            if (!same_root(a, left) || !same_root(b, right))
                && let Some(answer) =
                    self.decide_operand_comparison(MachineIntegerType::Int64, Relation::Equal, a, b)
            {
                return Some(answer != negate);
            }
        }
        let left_constant = self.wide_constant_from_equalities_view(left);
        let right_constant = self.wide_constant_from_equalities_view(right);
        if equality {
            let bounded = match (left_constant, right_constant) {
                (None, Some(value)) => self
                    .int64_interval_view(left)
                    .map(|bounds| (bounds, value as i64)),
                (Some(value), None) => self
                    .int64_interval_view(right)
                    .map(|bounds| (bounds, value as i64)),
                _ => None,
            };
            if bounded.is_some_and(|((lower, upper), value)| value < lower || value > upper) {
                return Some(negate);
            }
        }
        if let (Some(a), Some(b)) = (left_constant, right_constant) {
            let order = if view.format == MachineIntegerType::Int64 {
                (a as i64).cmp(&(b as i64))
            } else {
                a.cmp(&b)
            };
            return Some(match view.relation {
                Relation::Equal => a == b,
                Relation::NotEqual => a != b,
                Relation::Less => order.is_lt(),
                Relation::LessEqual => !order.is_gt(),
            });
        }
        // Replace only an endpoint that was not already a literal. Retain
        // the other operand's DAG handle instead of exporting its subtree.
        let replacement = |term: MachineOperandView<'_>, value: Option<u64>| {
            if term.uint64_constant().is_some() || term.int64_constant().is_some() {
                None
            } else {
                value.map(|value| {
                    if view.format == MachineIntegerType::Int64 && !equality {
                        OldMachineTerm::int64_constant(value as i64)
                    } else {
                        OldMachineTerm::uint64_constant(value)
                    }
                })
            }
        };
        let a = replacement(left, left_constant);
        let b = replacement(right, right_constant);
        if a.is_none() && b.is_none() {
            return None;
        }
        self.decide_operand_comparison(
            view.format,
            view.relation,
            a.as_ref().map(MachineOperandView::Old).unwrap_or(left),
            b.as_ref().map(MachineOperandView::Old).unwrap_or(right),
        )
    }

    /// Build a checking consequence without exporting shared operands. Native
    /// inputs keep their existing native condition and constructor behavior.
    pub(super) fn decide_operand_comparison(
        &self,
        format: MachineIntegerType,
        relation: crate::kernel::machine_integer::Relation,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::comparison::{ComparisonOperand, NativeComparisonView};
        if let (MachineOperandView::Old(left), MachineOperandView::Old(right)) = (left, right) {
            let (condition, truth) = crate::kernel::machine_integer::representation::comparison(
                format,
                relation,
                left.clone(),
                right.clone(),
            )?;
            self.decide(&condition).map(|answer| answer == truth)
        } else {
            self.decide(
                &NativeComparisonView {
                    format,
                    relation,
                    operands: [left, right]
                        .map(|operand| ComparisonOperand::Observation(operand.retain(format))),
                }
                .integer_condition(),
            )
        }
    }

    pub(super) fn has_written_operand_comparison(
        &self,
        format: MachineIntegerType,
        relation: CompareRelation,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        truth: bool,
    ) -> bool {
        self.has_condition_fact(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format,
                relation,
                [left, right],
            ),
            truth,
        )
    }

    pub(super) fn decide_written_operand_comparison(
        &self,
        format: MachineIntegerType,
        relation: CompareRelation,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<bool> {
        self.decide(
            &crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format,
                relation,
                [left, right],
            ),
        )
    }

    pub(super) fn has_operand_comparison(
        &self,
        format: MachineIntegerType,
        relation: crate::kernel::machine_integer::Relation,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> bool {
        use crate::kernel::machine_integer::comparison::{ComparisonOperand, NativeComparisonView};
        if let (MachineOperandView::Old(left), MachineOperandView::Old(right)) = (left, right) {
            crate::kernel::machine_integer::representation::comparison(
                format,
                relation,
                left.clone(),
                right.clone(),
            )
            .is_some_and(|(condition, truth)| self.has_condition_fact(condition, truth))
        } else {
            let view = NativeComparisonView {
                format,
                relation,
                operands: [left, right]
                    .map(|operand| ComparisonOperand::Observation(operand.retain(format))),
            };
            let Proposition::ConditionIs(condition, truth) = view.integer_proposition() else {
                unreachable!()
            };
            self.has_condition_fact(condition.old_form().clone(), truth)
        }
    }

    /// Strip bit-preserving conversions and signed additive identities by
    /// inspecting each root and querying only its selected operand.
    fn bitvector64_identity_base_view<'a>(
        &self,
        mut term: MachineOperandView<'a>,
    ) -> MachineOperandView<'a> {
        loop {
            if let Some((MachineIntegerType::Int64, op, [a, b])) = term.binary() {
                if matches!(op, MachineBinaryOp::Add | MachineBinaryOp::Subtract)
                    && self.wide_constant_from_equalities_view(b) == Some(0)
                {
                    term = a;
                    continue;
                }
                if op == MachineBinaryOp::Add
                    && self.wide_constant_from_equalities_view(a) == Some(0)
                {
                    term = b;
                    continue;
                }
            }
            if let Some((MachineCastSpelling::UInt64FromInt64, _, _, operand)) = term.cast() {
                term = operand;
                continue;
            }
            return term;
        }
    }

    pub(in crate::kernel) fn wide_constant_from_equalities(
        &self,
        term: &OldMachineTerm,
    ) -> Option<u64> {
        self.equality_graph.wide_constant(self, term)
    }

    pub(in crate::kernel) fn wide_constant_from_equalities_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<u64> {
        self.equality_graph.wide_constant_view(self, term)
    }

    /// Query wrapping int32 value equality maintained by the trusted graph.
    /// This performs no fact-component walk, arithmetic search, or state
    /// transport. `false` means unknown. Equal residues establish exact byte
    /// offsets only through the separate offset judgment's no-wrap guards.
    pub(in crate::kernel) fn int32_values_known_equal(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> bool {
        self.int32_values_known_equal_views(
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        )
    }

    pub(in crate::kernel) fn int32_values_known_equal_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> bool {
        self.equality_graph.are_int32_equal_views(left, right)
    }

    /// The other terms exact equality facts join to `term`: its equality
    /// component in the exact-premise adjacency index, less `term` itself,
    /// in canonical form. This enumerates evidence spellings; Boolean value
    /// equality uses `int32_values_known_equal`. Empty when no fact mentions it.
    ///
    /// Work is the class the search reaches and the edges inside it, never
    /// the whole fact set once the graph is built, so an index keyed by
    /// syntactic endpoints can also look an endpoint up under the spellings
    /// the premises make equal to it.
    pub(in crate::kernel) fn bitvector_equality_class_view(
        &self,
        term: &OldMachineTerm,
    ) -> Vec<SharedMachineIntegerTerm> {
        self.equality_graph
            .scalar_evidence_class_view(MachineOperandView::Old(term))
    }

    /// Retain one deterministic path made only from exact int32 equality
    /// conditions. SymbolicMemory-canonicalized and pointer-offset-derived graph
    /// edges deliberately remain for their own typed evidence kinds.
    pub(in crate::kernel) fn exact_bitvector_equality_path_evidence(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Option<Vec<BitvectorEqualityDerivationStep>> {
        self.exact_bitvector_equality_path_evidence_views(
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        )
    }

    pub(in crate::kernel) fn exact_bitvector_equality_path_evidence_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<Vec<BitvectorEqualityDerivationStep>> {
        self.equality_graph.exact_scalar_evidence_path(left, right)
    }

    pub(in crate::kernel) fn pointer_offset_congruence_evidence(
        &self,
        left: &AddressOffset,
        right: &AddressOffset,
    ) -> Option<PointerOffsetCongruenceEvidence> {
        if left == right {
            return Some(PointerOffsetCongruenceEvidence::Exact);
        }
        let exact_premise = Proposition::condition_is(
            OldConditionTerm::address_offset_equal(left.clone(), right.clone()),
            true,
        );
        if self.contains_assumed_exact(&exact_premise) {
            return Some(PointerOffsetCongruenceEvidence::ExactPremise(Box::new(
                exact_premise,
            )));
        }
        let mirrored_premise = Proposition::condition_is(
            OldConditionTerm::address_offset_equal(right.clone(), left.clone()),
            true,
        );
        if self.contains_assumed_exact(&mirrored_premise) {
            return Some(PointerOffsetCongruenceEvidence::ExactPremise(Box::new(
                mirrored_premise,
            )));
        }
        if let Some(premise) = self
            .equality_graph
            .exact_address_offset_equality_source(left, right)
        {
            return Some(PointerOffsetCongruenceEvidence::ExactPremise(Box::new(
                premise.clone(),
            )));
        }
        if let (Some(left), Some(right)) = (
            super::super::exact_wide_scaled_offset_constant(left, self),
            super::super::exact_wide_scaled_offset_constant(right, self),
        ) && left == right
        {
            return Some(PointerOffsetCongruenceEvidence::WideScaledConstant { value: left });
        }
        if let Some(evidence) = self.pointer_offset_element_index_evidence(left, right) {
            return Some(evidence);
        }
        match (left.view(), right.view()) {
            (OffsetView::Add(left_a, left_b), OffsetView::Add(right_a, right_b)) => {
                if let Some((first, second)) = self
                    .pointer_offset_congruence_evidence(left_a, right_a)
                    .zip(self.pointer_offset_congruence_evidence(left_b, right_b))
                {
                    return Some(PointerOffsetCongruenceEvidence::Add {
                        first: Box::new(first),
                        second: Box::new(second),
                        swapped: false,
                    });
                }

                self.pointer_offset_congruence_evidence(left_a, right_b)
                    .zip(self.pointer_offset_congruence_evidence(left_b, right_a))
                    .map(|(first, second)| PointerOffsetCongruenceEvidence::Add {
                        first: Box::new(first),
                        second: Box::new(second),
                        swapped: true,
                    })
            }
            (
                OffsetView::Int32Scaled {
                    index: left,
                    byte_width: left_width,
                },
                OffsetView::Int32Scaled {
                    index: right,
                    byte_width: right_width,
                },
            ) if left_width == right_width => self
                .exact_bitvector_equality_path_evidence_views(
                    left.operand_view(),
                    right.operand_view(),
                )
                .map(|path| PointerOffsetCongruenceEvidence::Int32Scaled {
                    byte_width: left_width,
                    path,
                })
                .or_else(|| {
                    self.direct_bitvector_equality_evidence_views(
                        left.operand_view(),
                        right.operand_view(),
                    )
                    .map(|equality| {
                        PointerOffsetCongruenceEvidence::Int32ScaledDerived {
                            byte_width: left_width,
                            equality,
                        }
                    })
                }),
            (
                OffsetView::Int64Scaled {
                    index: left,
                    byte_width: left_width,
                    unsigned: left_unsigned,
                },
                OffsetView::Int64Scaled {
                    index: right,
                    byte_width: right_width,
                    unsigned: right_unsigned,
                },
            ) if left_width == right_width && left_unsigned == right_unsigned => {
                Some(PointerOffsetCongruenceEvidence::Int64Scaled {
                    byte_width: left_width,
                    unsigned: left_unsigned,
                    path: self.exact_bitvector_equality_path_evidence_views(
                        left.operand_view(),
                        right.operand_view(),
                    )?,
                })
            }
            _ => None,
        }
    }

    fn pointer_offset_element_index_evidence(
        &self,
        left: &AddressOffset,
        right: &AddressOffset,
    ) -> Option<PointerOffsetCongruenceEvidence> {
        let byte_width = common_pointer_offset_element_width(left, right)?;
        let (left_index, right_index) = (
            shared_element_index_from_offset(left, byte_width)?,
            shared_element_index_from_offset(right, byte_width)?,
        );
        self.exact_bitvector_equality_path_evidence_views(
            left_index.operand_view(),
            right_index.operand_view(),
        )
        .map(|path| PointerOffsetCongruenceEvidence::ElementIndex { byte_width, path })
        .or_else(|| {
            self.direct_bitvector_equality_evidence_views(
                left_index.operand_view(),
                right_index.operand_view(),
            )
            .map(
                |equality| PointerOffsetCongruenceEvidence::ElementIndexDerived {
                    byte_width,
                    equality,
                },
            )
        })
    }

    pub(in crate::kernel) fn load_address_congruence_evidence(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Option<LoadAddressCongruenceEvidence> {
        let left = crate::kernel::eval::scalar_read_observation(MachineOperandView::Old(left))?;
        let right = crate::kernel::eval::scalar_read_observation(MachineOperandView::Old(right))?;
        let (left_point, left_pointer, left_kind) = (left.point, left.pointer, left.kind);
        let (right_point, right_pointer, right_kind) = (right.point, right.pointer, right.kind);
        // Congruence retains the exact state and read kind.
        if left_point != right_point
            || left_kind != right_kind
            || left_pointer.base != right_pointer.base
        {
            return None;
        }
        Some(LoadAddressCongruenceEvidence {
            offset: self
                .pointer_offset_congruence_evidence(&left_pointer.offset, &right_pointer.offset)?,
            left_pointer,
            right_pointer,
        })
    }

    pub(super) fn checking_word32_shared_root(
        &self,
        root: &crate::kernel::KernelTerm,
    ) -> crate::kernel::KernelTerm {
        self.equality_graph.checking_word32_root(root, |child| {
            self.indexed_exact_int32_constant_view(MachineOperandView::Shared(child))
                .map(|(value, _)| value as u32)
        })
    }

    fn shared_word_checking_form(&self, condition: &OldConditionTerm) -> Option<OldConditionTerm> {
        // Preserve written cast roots here, as the native simplifier does.
        // Reading sigma away before substituting a child constant would enable
        // a different subsequent mask-range rule.
        if let Some(view) =
            crate::kernel::machine_integer::comparison::structural_native_comparison_view(
                condition, true,
            )
            && matches!(
                view.format,
                MachineIntegerType::Int32
                    | MachineIntegerType::UInt32
                    | MachineIntegerType::Int64
                    | MachineIntegerType::UInt64
            )
            && matches!(
                view.relation,
                crate::kernel::machine_integer::Relation::Less
                    | crate::kernel::machine_integer::Relation::LessEqual
                    | crate::kernel::machine_integer::Relation::Equal
            )
        {
            let operands = view
                .operands
                .each_ref()
                .map(|operand| match operand.operand_view() {
                    MachineOperandView::Shared(root) => {
                        Some(if view.format.format().bits() == 64 {
                            crate::kernel::proof::term_rewrite::TermRewrite::checking_wide_syntax(
                                root,
                            )
                        } else {
                            self.checking_word32_shared_root(root)
                        })
                    }
                    MachineOperandView::Old(_) => None,
                });
            let changed = operands
                .iter()
                .zip(view.operands.iter())
                .any(|(read, written)| match written.operand_view() {
                    MachineOperandView::Shared(root) => {
                        read.as_ref().is_some_and(|read| read != root)
                    }
                    MachineOperandView::Old(_) => false,
                });
            if changed {
                let normalized =
                    crate::kernel::machine_integer::comparison::condition_for_operand_views(
                        view.format,
                        match view.relation {
                            crate::kernel::machine_integer::Relation::Less => {
                                CompareRelation::LessThan
                            }
                            crate::kernel::machine_integer::Relation::LessEqual => {
                                CompareRelation::LessEqual
                            }
                            crate::kernel::machine_integer::Relation::Equal => {
                                CompareRelation::Equal
                            }
                            crate::kernel::machine_integer::Relation::NotEqual => unreachable!(),
                        },
                        std::array::from_fn(|i| {
                            operands[i]
                                .as_ref()
                                .map(MachineOperandView::Shared)
                                .unwrap_or_else(|| view.operands[i].operand_view())
                        }),
                    );
                return Some(normalized);
            }
        }
        None
    }

    pub(in crate::kernel) fn simplify_condition_under_assumptions(
        &self,
        condition: &OldConditionTerm,
    ) -> OldConditionTerm {
        if let Some(read) = self.shared_word_checking_form(condition) {
            return read;
        }
        match condition {
            OldConditionTerm::AlgebraicEqual(left, right) => self
                .decide_algebraic_equality(left, right)
                .map(OldConditionTerm::Constant)
                .unwrap_or_else(|| condition.clone()),
            OldConditionTerm::Constant(value) => OldConditionTerm::Constant(*value),
            OldConditionTerm::Variable(variable) => OldConditionTerm::Variable(*variable),
            OldConditionTerm::Float32(FloatCondition::Comparison {
                operator,
                left,
                right,
            }) => OldConditionTerm::float32_compare(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
                *operator,
            ),
            OldConditionTerm::Float32(FloatCondition::Classification {
                classification,
                value,
            }) => OldConditionTerm::float32_classification(
                self.simplify_bitvector_under_assumptions(value),
                *classification,
            ),
            OldConditionTerm::Float64(FloatCondition::Comparison {
                operator,
                left,
                right,
            }) => OldConditionTerm::float64_compare(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
                *operator,
            ),
            OldConditionTerm::Float64(FloatCondition::Classification {
                classification,
                value,
            }) => OldConditionTerm::float64_classification(
                self.simplify_bitvector_under_assumptions(value),
                *classification,
            ),
            OldConditionTerm::AddressOffsetEqual(left, right) => {
                OldConditionTerm::address_offset_equal(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                )
            }
            OldConditionTerm::PointerEqual(..) => condition.clone(),
            OldConditionTerm::AddressEqual(left, right) => {
                OldConditionTerm::address_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            // Integer arithmetic has no memory loads; assumption-driven
            // simplification is intentionally limited to its local exact
            // constructors until the checked arithmetic planner lands.
            OldConditionTerm::IntegerLessThan(left, right) => {
                OldConditionTerm::integer_less_than(left.as_ref().clone(), right.as_ref().clone())
            }
            OldConditionTerm::IntegerLessEqual(left, right) => {
                OldConditionTerm::integer_less_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            OldConditionTerm::IntegerGreaterThan(left, right) => {
                OldConditionTerm::integer_greater_than(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                )
            }
            OldConditionTerm::IntegerGreaterEqual(left, right) => {
                OldConditionTerm::integer_greater_equal(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                )
            }
            OldConditionTerm::IntegerEqual(left, right) => {
                OldConditionTerm::integer_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            OldConditionTerm::IntegerNotEqual(left, right) => {
                OldConditionTerm::integer_not_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            // A `Bool` value is kept unless the facts decide it.
            condition if condition.is_bool_value_form() => self
                .decide(condition)
                .map(OldConditionTerm::Constant)
                .unwrap_or_else(|| condition.clone()),
            condition => {
                let (op, left, right) = condition
                    .as_bitvector_comparison()
                    .expect("every other condition has its own arm");
                op.build(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
        }
    }

    pub(in crate::kernel) fn simplify_bitvector_under_assumptions(
        &self,
        term: &OldMachineTerm,
    ) -> OldMachineTerm {
        if let Some(value) = self.bitvector_constant_from_direct_equalities(term) {
            return OldMachineTerm::constant(value);
        }
        match term {
            OldMachineTerm::ThreadHandle(_) => term.clone(),
            OldMachineTerm::Constant { .. } => term.clone(),
            OldMachineTerm::Variable(variable) => OldMachineTerm::Variable(*variable),
            cast_term!(UInt32From64, value) => match self.wide_constant_from_equalities(value) {
                Some(bits) => OldMachineTerm::constant(bits as u32),
                None => {
                    OldMachineTerm::uint32_from_64(self.simplify_bitvector_under_assumptions(value))
                }
            },
            // A narrowing conversion inside its destination range is its
            // operand's carrier (`narrowed_casts`); otherwise it stays the
            // conversion of its simplified operand.
            OldMachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination,
            } => match self.narrowed_cast_carrier(term) {
                Some(carrier) => self.simplify_bitvector_under_assumptions(&carrier),
                None => OldMachineTerm::machine_integer_cast(
                    *source,
                    *destination,
                    self.simplify_bitvector_under_assumptions(value),
                ),
            },
            OldMachineTerm::If {
                condition,
                then_term,
                else_term,
            } => match self.decide(condition) {
                Some(true) => self.simplify_bitvector_under_assumptions(then_term),
                Some(false) => self.simplify_bitvector_under_assumptions(else_term),
                None => OldMachineTerm::if_then_else(
                    condition.as_ref().clone(),
                    self.simplify_bitvector_under_assumptions(then_term),
                    self.simplify_bitvector_under_assumptions(else_term),
                ),
            },
            OldMachineTerm::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => OldMachineTerm::range_fold(
                self.simplify_bitvector_under_assumptions(start),
                self.simplify_bitvector_under_assumptions(end),
                self.simplify_bitvector_under_assumptions(initial),
                *accumulator,
                *item,
                self.simplify_bitvector_under_assumptions(body),
            ),
            OldMachineTerm::PureFunctionApplication { name, arguments } => {
                OldMachineTerm::rebuild_pure_application(
                    name.clone(),
                    arguments
                        .iter()
                        .map(|argument| self.simplify_bitvector_under_assumptions(argument))
                        .collect(),
                )
            }
            // Rule C1: a decided `Bool` casts to 1 or 0.
            OldMachineTerm::BoolCast { value, .. } => match self.decide(value) {
                Some(value) => OldMachineTerm::constant(u32::from(value)),
                None => term.clone(),
            },
            OldMachineTerm::ClickFunctionApplication { .. }
            | OldMachineTerm::PureApplicationCount(_)
            | OldMachineTerm::AlgebraicMatch { .. }
            | OldMachineTerm::IntegerToMachine { .. } => term.clone(),
            OldMachineTerm::MemoryLoad(memory, pointer, kind) => {
                OldMachineTerm::read_named(memory.clone(), pointer.clone(), *kind)
            }
            OldMachineTerm::IntegerAddress(_, _) => term.clone(),
            term => match (term.as_binary(), term.as_unary()) {
                (Some((op, left, right)), _) => op.build(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                ),
                (_, Some((op, value))) => {
                    op.build(self.simplify_bitvector_under_assumptions(value))
                }
                _ => unreachable!("every other variant has its own arm"),
            },
        }
    }

    pub(in crate::kernel) fn order_facts_force_equal(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> bool {
        self.order_facts_force_equal_views(
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        )
    }

    pub(super) fn order_facts_force_equal_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> bool {
        self.has_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            left,
            right,
            true,
        ) && self.has_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::LessThan,
            left,
            right,
            false,
        ) || self.has_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            right,
            left,
            true,
        ) && self.has_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::LessThan,
            right,
            left,
            false,
        ) || self.has_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::GreaterEqual,
            left,
            right,
            true,
        ) && self.has_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::GreaterThan,
            left,
            right,
            false,
        ) || self.has_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::GreaterEqual,
            right,
            left,
            true,
        ) && self.has_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::GreaterThan,
            right,
            left,
            false,
        )
    }

    pub(in crate::kernel) fn range_facts_force_equal(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> bool {
        self.range_facts_force_equal_views(
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        )
    }

    pub(super) fn range_facts_force_equal_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> bool {
        let pair = |a: MachineOperandView<'_>, b: MachineOperandView<'_>| {
            a.variable().copied().zip(b.word32_constant())
        };
        let Some((variable, constant)) = pair(left, right).or_else(|| pair(right, left)) else {
            return false;
        };
        let term = OldMachineTerm::Variable(variable);
        let Some((lower, upper)) = self.indexed_constant_interval(&term) else {
            return false;
        };
        let (lower, upper) =
            self.checked_scalar_facts
                .past_exclusions(MachineOperandView::Old(&term), lower, upper);
        lower == upper && lower == i64::from(constant as i32)
    }

    #[cfg(test)]
    pub(in crate::kernel) fn signed_constant_known_equal(
        &self,
        term: &OldMachineTerm,
    ) -> Option<i64> {
        self.signed_constant_known_equal_view(MachineOperandView::Old(term))
    }

    pub(in crate::kernel) fn signed_constant_known_equal_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<i64> {
        if let Some(value) = term.word32_constant() {
            return Some(i64::from(value as i32));
        }
        if let MachineOperandView::Old(term) = term
            && let Some(value) = self.equality_graph.known_atom_constant(term)
        {
            return Some(value);
        }
        match self.equality_graph.scalar_normalization_class_view(term)?.1 {
            SignedConstantResolution::Known(value) => Some(value),
            _ => None,
        }
    }

    pub(in crate::kernel) fn signed_constant_after_equality_normalization(
        &self,
        term: &OldMachineTerm,
    ) -> Option<i64> {
        // The walk re-resolves the same subterms across goals and claims;
        // memoize by fact-set content identity exactly like `decide`.
        let _scope = PureFactContextIdScope::enter(self);
        let key = (_scope.id, term.clone());
        if let Some(hit) = CONSTANT_NORMALIZATION_MEMO.with(|memo| memo.borrow().get(&key).copied())
        {
            return hit;
        }
        let epoch_before = INCOMPLETE_REASONING_EPOCH.with(Cell::get);
        let result = self.signed_constant_after_equality_normalization_unmemoized(term);
        if result.is_some() || INCOMPLETE_REASONING_EPOCH.with(Cell::get) == epoch_before {
            CONSTANT_NORMALIZATION_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DECIDE_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(key, result);
            });
        }
        result
    }

    fn signed_constant_after_equality_normalization_unmemoized(
        &self,
        term: &OldMachineTerm,
    ) -> Option<i64> {
        match self.constant_class_resolution(term, &mut BTreeSet::new()) {
            SignedConstantResolution::Known(value) => Some(value),
            SignedConstantResolution::Unknown | SignedConstantResolution::Ambiguous => None,
        }
    }

    /// Read a settled constant from the equality class, or resolve its
    /// conditional members. Unregistered arithmetic folds from its operands.
    /// Do not search other states for equal loads here: a missing relation
    /// must be established before this fast checking query.
    fn constant_class_resolution(
        &self,
        term: &OldMachineTerm,
        visiting: &mut BTreeSet<u64>,
    ) -> SignedConstantResolution {
        self.constant_class_resolution_view(MachineOperandView::Old(term), visiting)
    }

    pub(in crate::kernel) fn known_signed_constant_after_normalization_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<i64> {
        match term {
            MachineOperandView::Old(term) => self.known_signed_constant_after_normalization(term),
            _ => match self.constant_class_resolution_view(term, &mut BTreeSet::new()) {
                SignedConstantResolution::Known(value) => Some(value),
                _ => None,
            },
        }
    }

    fn constant_class_resolution_view(
        &self,
        term: MachineOperandView<'_>,
        visiting: &mut BTreeSet<u64>,
    ) -> SignedConstantResolution {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(value) = term.word32_constant().map(|value| i64::from(value as i32)) {
            return SignedConstantResolution::Known(value);
        }
        let classes = &self.equality_graph;
        if let Some((id, constant)) = classes.scalar_normalization_class_view(term) {
            if constant != SignedConstantResolution::Unknown || !visiting.insert(id) {
                return constant;
            }
            let mut result = SignedConstantResolution::Unknown;
            for conditional in classes.scalar_conditional_members(id) {
                result = result.merge(
                    self.conditional_constant_resolution_view(conditional.operand_view(), visiting),
                );
            }
            visiting.remove(&id);
            return result;
        }
        if term.conditional_view().is_some() {
            return self.conditional_constant_resolution_view(term, visiting);
        }
        let MachineOperandView::Old(term) = term else {
            return SignedConstantResolution::Unknown;
        };
        match term {
            OldMachineTerm::If { .. } => self.conditional_constant_resolution(term, visiting),
            _ => crate::kernel::equality_graph::fold_arithmetic(term, |operand| {
                self.constant_class_resolution(operand, visiting)
            }),
        }
    }

    fn conditional_constant_resolution(
        &self,
        term: &OldMachineTerm,
        visiting: &mut BTreeSet<u64>,
    ) -> SignedConstantResolution {
        self.conditional_constant_resolution_view(MachineOperandView::Old(term), visiting)
    }

    fn conditional_constant_resolution_view(
        &self,
        term: MachineOperandView<'_>,
        visiting: &mut BTreeSet<u64>,
    ) -> SignedConstantResolution {
        let Some((condition, [left, right])) = term.conditional() else {
            return SignedConstantResolution::Unknown;
        };
        match self.decide(&condition) {
            Some(condition) => {
                self.constant_class_resolution_view(if condition { left } else { right }, visiting)
            }
            None => SignedConstantResolution::Unknown,
        }
    }

    /// Apply the existing guard/arm and fold reductions before comparing
    /// retained results. Unscoped roots keep their existing dispatch and work.
    fn decide_shared_conditional_comparison(&self, condition: &OldConditionTerm) -> Option<bool> {
        use crate::kernel::machine_integer::comparison::{
            condition_for_operand_views, structural_comparison_view,
        };
        let view = structural_comparison_view(condition)?;
        let operands = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let contains_fold = |operand: MachineOperandView<'_>| matches!(operand, MachineOperandView::Shared(root) if root.has_machine_folds());
        if !operands.iter().any(|operand| {
            (matches!(operand, MachineOperandView::Shared(_))
                && operand.conditional_view().is_some())
                || contains_fold(*operand)
        }) {
            return None;
        }
        let original = operands.map(|operand| operand.retain(view.format));
        let reduced = operands.map(|mut operand| {
            // Consume the selected chain once. Re-entering comparison dispatch
            // at every arm would re-key every remaining suffix quadratically.
            while let Some((guard, arms)) = operand.conditional() {
                let selected = self.decide(&guard).or_else(|| {
                    (arms[0].retain(view.format) == arms[1].retain(view.format)).then_some(true)
                });
                let Some(value) = selected else { break };
                crate::instrumentation::record_deterministic_work(1);
                operand = arms[if value { 0 } else { 1 }];
            }
            if contains_fold(operand) {
                self.simplify_machine_operand_under_assumptions(operand, view.format)
            } else {
                operand.retain(view.format)
            }
        });
        if reduced == original {
            return None;
        }
        let reduced_condition = condition_for_operand_views(
            view.format,
            view.relation,
            reduced.each_ref().map(|operand| operand.operand_view()),
        );
        self.decide(&reduced_condition)
            .map(|value| value != view.negated)
    }

    fn decide_shared_signed_constant_order(&self, condition: &OldConditionTerm) -> Option<bool> {
        use crate::kernel::machine_integer::{Relation, comparison::native_comparison_view};
        let view = native_comparison_view(condition, true)?;
        if view.format != MachineIntegerType::Int32 {
            return None;
        }
        let left = self.signed_constant_known_equal_view(view.operands[0].operand_view())?;
        let right = self.signed_constant_known_equal_view(view.operands[1].operand_view())?;
        Some(match view.relation {
            Relation::Equal => left == right,
            Relation::NotEqual => left != right,
            Relation::Less => left < right,
            Relation::LessEqual => left <= right,
        })
    }

    pub(super) fn decide_signed_comparison_from_equal_constants_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        compare: impl FnOnce(i64, i64) -> bool,
    ) -> Option<bool> {
        Some(compare(
            self.signed_constant_known_equal_view(left)?,
            self.signed_constant_known_equal_view(right)?,
        ))
    }
}

/// `condition` with each read of a stored cell replaced by its stored value
/// (`eval::comparison_form`).
fn read_over_write_condition(condition: &OldConditionTerm) -> Option<OldConditionTerm> {
    match crate::kernel::eval::comparison_form(&Proposition::condition_is(condition.clone(), true))?
    {
        Proposition::ConditionIs(resolved, true) if resolved.old_form() != condition => {
            Some(resolved.old_form().clone())
        }
        _ => None,
    }
}

#[cfg(test)]
mod owned_anchor_tests {
    use super::*;

    fn pointer(id: u64) -> Address {
        Address::symbolic(Variable(991_000 + id))
    }

    fn owner_of(pointers: &[Address]) -> Proposition {
        Proposition::ResourceComposition(ResourceContext::new().unchecked_with_facts(
            pointers.iter().map(|pointer| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    pointer.clone(),
                    0u32.into(),
                    1u32.into(),
                    8,
                ))
            }),
        ))
    }

    mod scaling_tests {
        use super::*;
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/decision/owned_anchor_tests.rs"
        );
    }
}

#[cfg(test)]
mod shared_wide_decision_tests {
    use super::*;
    use crate::kernel::{KernelTerm, KernelType, SharedMachineIntegerTerm};

    #[test]
    fn wide_constant_decision_reads_shared_values_and_intervals() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(997561));
            let operand = SharedMachineIntegerTerm::from_shared(
                format,
                KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [variable.clone(), variable],
                ),
            )
            .unwrap();
            let observation = || IntegerTerm::Machine(operand.clone());
            let equal =
                OldConditionTerm::integer_equal(observation(), IntegerTerm::constant(7.into()));
            let context = PureFactContext::new().assume_condition(equal, true);
            for (query, expected) in [
                (
                    OldConditionTerm::integer_less_than(
                        observation(),
                        IntegerTerm::constant(8.into()),
                    ),
                    Some(true),
                ),
                (
                    OldConditionTerm::integer_greater_than(
                        observation(),
                        IntegerTerm::constant(8.into()),
                    ),
                    Some(false),
                ),
                (
                    OldConditionTerm::integer_not_equal(
                        observation(),
                        IntegerTerm::constant(7.into()),
                    ),
                    Some(false),
                ),
            ] {
                assert_eq!(context.decide_wide_constant_comparison(&query), expected);
            }
            let ranged = PureFactContext::new().assume_condition(
                OldConditionTerm::integer_less_equal(
                    observation(),
                    IntegerTerm::constant(10.into()),
                ),
                true,
            );
            if format == MachineIntegerType::Int64 {
                assert_eq!(
                    ranged.decide_wide_constant_comparison(&OldConditionTerm::integer_equal(
                        observation(),
                        IntegerTerm::constant(11.into())
                    )),
                    Some(false)
                );
                assert_eq!(
                    ranged.decide_wide_constant_comparison(&OldConditionTerm::integer_equal(
                        observation(),
                        IntegerTerm::constant(9.into())
                    )),
                    None
                );
            }
            assert!(!operand.has_boxed_operand());
        }
    }
}

#[cfg(test)]
mod exact_word_order_tests {
    use super::*;
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView as V};

    fn query(
        format: MachineIntegerType,
        relation: CompareRelation,
        term: V<'_>,
        bound: u32,
    ) -> OldConditionTerm {
        condition_for_operand_views(
            format,
            relation,
            [term, V::Old(&OldMachineTerm::constant(bound))],
        )
    }

    #[test]
    fn adjacent_bound_views_preserve_answers_mirrors_and_sources() {
        let _session = crate::kernel::VerificationSession::enter();
        let term = OldMachineTerm::add(
            OldMachineTerm::Variable(Variable(189301)),
            OldMachineTerm::Variable(Variable(189302)),
        );
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            let root = KernelTermImport::default()
                .machine_arithmetic(format, &term)
                .unwrap();
            for (relation, source_relation, source_bound) in [
                (CompareRelation::LessThan, CompareRelation::LessEqual, 9),
                (CompareRelation::LessEqual, CompareRelation::LessThan, 11),
                (
                    CompareRelation::GreaterThan,
                    CompareRelation::GreaterEqual,
                    11,
                ),
                (
                    CompareRelation::GreaterEqual,
                    CompareRelation::GreaterThan,
                    9,
                ),
            ] {
                let native = query(format, relation, V::Old(&term), 10);
                let shared = query(format, relation, V::Shared(&root), 10);
                let source = query(format, source_relation, V::Old(&term), source_bound);
                for truth in [None, Some(false), Some(true)] {
                    let context = truth.map_or_else(PureFactContext::new, |truth| {
                        PureFactContext::new().assume_condition(source.clone(), truth)
                    });
                    assert_eq!(
                        context.decide_exact_word_constant_order(&native, format),
                        truth
                    );
                    let exports = KernelTermExport::machine_export_count();
                    let (answer, used) = collect_consulted_premises(|| {
                        capture_implicit_consulted_premises(|| {
                            context.decide_exact_word_constant_order(&shared, format)
                        })
                    });
                    assert_eq!(answer, truth, "{native:?}");
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    if let Some(truth) = truth {
                        assert!(
                            used.contains(&Proposition::condition_is(source.clone(), truth)),
                            "{used:?}"
                        );
                    }
                    let mirrored = match relation {
                        CompareRelation::LessThan => CompareRelation::GreaterThan,
                        CompareRelation::LessEqual => CompareRelation::GreaterEqual,
                        CompareRelation::GreaterThan => CompareRelation::LessThan,
                        CompareRelation::GreaterEqual => CompareRelation::LessEqual,
                        _ => unreachable!(),
                    };
                    let mirrored = condition_for_operand_views(
                        format,
                        mirrored,
                        [V::Old(&OldMachineTerm::constant(10)), V::Shared(&root)],
                    );
                    assert_eq!(
                        context.decide_exact_word_constant_order(&mirrored, format),
                        truth
                    );
                }
            }
        }
    }

    #[test]
    fn adjacent_bound_views_keep_signed_and_unsigned_endpoints() {
        use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp};
        let _session = crate::kernel::VerificationSession::enter();
        for (format, minimum, maximum) in [
            (MachineIntegerType::Int32, i32::MIN as u32, i32::MAX as u32),
            (MachineIntegerType::UInt32, 0, u32::MAX),
        ] {
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(189311));
            let root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [variable.clone(), variable],
            );
            let exports = KernelTermExport::machine_export_count();
            for (relation, bound, answer) in [
                (CompareRelation::LessThan, minimum, false),
                (CompareRelation::GreaterEqual, minimum, true),
                (CompareRelation::LessEqual, maximum, true),
                (CompareRelation::GreaterThan, maximum, false),
            ] {
                assert_eq!(
                    PureFactContext::new().decide_exact_word_constant_order(
                        &query(format, relation, V::Shared(&root), bound),
                        format
                    ),
                    Some(answer)
                );
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/decision/exact_word_order_tests.rs"
        );
    }
}

#[cfg(test)]
mod shared_order_pipeline_tests {
    use super::*;
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{KernelTermImport, MachineBinaryOp as Op};

    #[test]
    fn retained_model_arithmetic_uses_native_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let x = OldMachineTerm::Variable(Variable(997691));
        let y = OldMachineTerm::Variable(Variable(997692));
        let sum = OldMachineTerm::logical_machine_binary(ty, Op::Add, x.clone(), 1u32.into());
        let native = OldConditionTerm::signed_less_equal(0u32.into(), sum.clone());
        let shared =
            crate::kernel::machine_integer::comparison::retained_arithmetic_comparison(&native)
                .unwrap();
        let facts = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_less_equal(0u32.into(), x.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(x.clone(), 2u32.into()),
                true,
            );
        assert_eq!(facts.decide(&native), Some(true));
        assert_eq!(facts.decide(&shared), Some(true), "{shared:?}");
        let difference = OldMachineTerm::logical_machine_binary(ty, Op::Subtract, x, y.clone());
        let native = OldConditionTerm::equal(y, difference);
        let shared =
            crate::kernel::machine_integer::comparison::retained_arithmetic_comparison(&native)
                .unwrap();
        let empty = PureFactContext::new();
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        assert!(empty.condition_matches(&native, &shared));
        assert!(empty.condition_matches(&shared, &native));
        assert!(
            !empty.condition_matches(&shared, &OldConditionTerm::equal(0u32.into(), 1u32.into()))
        );
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
        assert_eq!(
            empty.assume_condition(native, true).decide(&shared),
            Some(true)
        );
    }

    // Keep each ordinary regression small while covering the same operation,
    // literal, equality-context and comparison combinations.
    fn check_order_terms(format: MachineIntegerType, terms: Vec<OldMachineTerm>) {
        let mut differences = Vec::new();
        let x = OldMachineTerm::Variable(Variable(997601));
        let y = OldMachineTerm::Variable(Variable(997602));
        for value in [None, Some(0u32), Some(1), Some(7), Some(u32::MAX)] {
            let facts = match value {
                None => PureFactContext::new(),
                Some(value) => PureFactContext::new()
                    .assume_condition(OldConditionTerm::equal(x.clone(), value.into()), true),
            };
            for term in &terms {
                for right in [x.clone(), y.clone(), 0u32.into(), 1u32.into(), 7u32.into()] {
                    for relation in [CompareRelation::LessThan, CompareRelation::LessEqual] {
                        let native = OldConditionTerm::Compare {
                            format,
                            relation,
                            left: Box::new(term.clone()),
                            right: Box::new(right.clone()),
                        };
                        let roots = [term, &right].map(|t| {
                            KernelTermImport::default()
                                .machine_arithmetic(format, t)
                                .unwrap()
                        });
                        let shared = condition_for_operand_views(
                            format,
                            relation,
                            roots.each_ref().map(MachineOperandView::Shared),
                        );
                        let actual = facts.decide(&shared);
                        let expected = facts.decide(&native);
                        if actual != expected && differences.len() < 100 {
                            differences.push(format!(
                                "{format:?} {value:?}: {native:?}: {actual:?} != {expected:?}"
                            ));
                        }
                    }
                }
            }
        }
        assert!(differences.is_empty(), "{}", differences.join("\n"));
    }

    macro_rules! operation_parity {
        ($(#[$attr:meta])* $name:ident, $format:ident, $op:ident) => {
            #[test]
            $(#[$attr])*
            fn $name() {
                let _session = crate::kernel::VerificationSession::enter();
                let format = MachineIntegerType::$format;
                let x = OldMachineTerm::Variable(Variable(997601));
                let y = OldMachineTerm::Variable(Variable(997602));
                let terms = [x.clone(), y, 0u32.into(), 1u32.into(), 7u32.into()].map(|right| {
                    OldMachineTerm::logical_machine_binary(format, Op::$op, x.clone(), right)
                });
                check_order_terms(format, terms.to_vec());
            }
        };
    }
    operation_parity!(signed_add_checking_parity, Int32, Add);
    operation_parity!(signed_subtract_checking_parity, Int32, Subtract);
    operation_parity!(signed_multiply_checking_parity, Int32, Multiply);
    operation_parity!(signed_divide_checking_parity, Int32, Divide);
    operation_parity!(signed_remainder_checking_parity, Int32, Remainder);
    operation_parity!(signed_bitwiseand_checking_parity, Int32, BitwiseAnd);
    operation_parity!(signed_bitwiseor_checking_parity, Int32, BitwiseOr);
    operation_parity!(signed_bitwisexor_checking_parity, Int32, BitwiseXor);
    operation_parity!(unsigned_add_checking_parity, UInt32, Add);
    operation_parity!(unsigned_subtract_checking_parity, UInt32, Subtract);
    operation_parity!(unsigned_multiply_checking_parity, UInt32, Multiply);
    operation_parity!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: 0.6s in the parallel gate"]
        unsigned_divide_checking_parity,
        UInt32,
        Divide
    );
    operation_parity!(unsigned_remainder_checking_parity, UInt32, Remainder);
    operation_parity!(unsigned_bitwiseand_checking_parity, UInt32, BitwiseAnd);
    operation_parity!(unsigned_bitwiseor_checking_parity, UInt32, BitwiseOr);
    operation_parity!(unsigned_bitwisexor_checking_parity, UInt32, BitwiseXor);

    macro_rules! nested_parity {
        ($(#[$attr:meta])* $name:ident, $format:ident, $outer:ident) => {
            #[test]
            $(#[$attr])*
            fn $name() {
                let _session = crate::kernel::VerificationSession::enter();
                let format = MachineIntegerType::$format;
                let x = OldMachineTerm::Variable(Variable(997601));
                let y = OldMachineTerm::Variable(Variable(997602));
                let mut terms = vec![x.clone(), y.clone()];
                for inner in [Op::Add, Op::Subtract, Op::BitwiseXor] {
                    let inner =
                        OldMachineTerm::logical_machine_binary(format, inner, x.clone(), y.clone());
                    for last in [x.clone(), y.clone()] {
                        terms.push(OldMachineTerm::logical_machine_binary(
                            format,
                            Op::$outer,
                            inner.clone(),
                            last,
                        ));
                    }
                }
                check_order_terms(format, terms);
            }
        };
    }
    nested_parity!(signed_nested_add_checking_parity, Int32, Add);
    nested_parity!(signed_nested_subtract_checking_parity, Int32, Subtract);
    nested_parity!(signed_nested_bitwisexor_checking_parity, Int32, BitwiseXor);
    nested_parity!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: 0.8s in the parallel gate"]
        unsigned_nested_add_checking_parity,
        UInt32,
        Add
    );
    nested_parity!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: 0.7s in the parallel gate"]
        unsigned_nested_subtract_checking_parity,
        UInt32,
        Subtract
    );
    nested_parity!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: 0.7s in the parallel gate"]
        unsigned_nested_bitwisexor_checking_parity,
        UInt32,
        BitwiseXor
    );

    #[test]
    fn shared_order_preserves_transitive_constant_contexts() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = OldMachineTerm::Variable(Variable(997601));
        let y = OldMachineTerm::Variable(Variable(997602));
        let z = OldMachineTerm::Variable(Variable(997603));
        let facts = PureFactContext::new()
            .assume_condition(OldConditionTerm::equal(x.clone(), z.clone()), true)
            .assume_condition(OldConditionTerm::equal(z, 1u32.into()), true);
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            for op in [Op::Add, Op::Multiply, Op::BitwiseAnd] {
                let term = OldMachineTerm::logical_machine_binary(format, op, x.clone(), y.clone());
                let root = KernelTermImport::default()
                    .machine_arithmetic(format, &term)
                    .unwrap();
                for bound in [0, 1, 7] {
                    let bound = OldMachineTerm::constant(bound);
                    for relation in [CompareRelation::LessThan, CompareRelation::LessEqual] {
                        let native = OldConditionTerm::machine_compare(
                            format,
                            relation,
                            term.clone(),
                            bound.clone(),
                        );
                        let shared = condition_for_operand_views(
                            format,
                            relation,
                            [
                                MachineOperandView::Shared(&root),
                                MachineOperandView::Old(&bound),
                            ],
                        );
                        assert_eq!(facts.decide(&shared), facts.decide(&native), "{native:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn shared_zero_addend_order_is_reflexive_without_export() {
        use crate::kernel::{KernelTerm, KernelTermExport, KernelType, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let x = KernelTerm::variable(KernelType::Program(format.program_type()), Variable(997621));
        let zero = KernelTermImport::default()
            .machine_arithmetic(format, &0u32.into())
            .unwrap();
        let sum = KernelTerm::machine_binary_shared(format, Op::Add, [x.clone(), zero]);
        let observed = |root| {
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap())
        };
        let query = OldConditionTerm::integer_less_than(observed(sum), observed(x));
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(PureFactContext::new().decide(&query), Some(false));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/decision/shared_order_pipeline_tests.rs"
        );
    }
}

#[cfg(test)]
mod shared_equality_dispatch_tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp as Op, SharedMachineIntegerTerm,
    };

    #[test]
    fn wide_mask_zero_keeps_shared_bounds_and_selected_evidence() {
        use crate::kernel::MachineOperandView as V;
        use crate::kernel::machine_integer::comparison::condition_for_operand_views;
        for mask in [0, 8, 24, 1u64 << 63] {
            for reversed in [false, true] {
                let _session = crate::kernel::VerificationSession::enter();
                let ty = MachineIntegerType::UInt64;
                let x =
                    KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(983001));
                let y =
                    KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(983002));
                let sum = KernelTerm::machine_binary_shared(ty, Op::Add, [x, y]);
                let literal = |n| {
                    crate::kernel::KernelTermImport::default()
                        .machine_arithmetic(ty, &OldMachineTerm::uint64_constant(n))
                        .unwrap()
                };
                let mask_term = literal(mask);
                let operands = if reversed {
                    [mask_term, sum.clone()]
                } else {
                    [sum.clone(), mask_term]
                };
                let masked = KernelTerm::machine_binary_shared(ty, Op::BitwiseAnd, operands);
                let zero = literal(0);
                let condition = condition_for_operand_views(
                    ty,
                    CompareRelation::Equal,
                    [V::Shared(&masked), V::Shared(&zero)],
                );
                let limit = OldMachineTerm::uint64_constant(if mask == 0 {
                    1
                } else {
                    1 << mask.trailing_zeros()
                });
                let guard = condition_for_operand_views(
                    ty,
                    CompareRelation::LessThan,
                    [V::Shared(&sum), V::Old(&limit)],
                );
                let parent = PureFactContext::new();
                let context = parent.clone().assume_condition(guard.clone(), true);
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(context.decide(&condition), Some(true));
                let not_equal = OldConditionTerm::integer_not_equal(
                    IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(ty, masked.clone()).unwrap(),
                    ),
                    IntegerTerm::constant_i64(0),
                );
                assert_eq!(context.decide(&not_equal), Some(false));
                let mut used = crate::kernel::eval::pointer_tags::UsedFacts::new();
                assert_eq!(context.decide_citing(&condition, &mut used), Some(true));
                assert!(used.complete);
                if mask != 0 {
                    assert_eq!(used.premises, vec![Proposition::condition_is(guard, true)]);
                    assert_eq!(
                        parent.decide_masked_zero(
                            V::Shared(&masked),
                            V::Shared(&zero),
                            &mut Default::default()
                        ),
                        None
                    );
                } else {
                    assert!(used.premises.is_empty());
                }
                if mask != 0 {
                    let false_guard = condition_for_operand_views(
                        ty,
                        CompareRelation::LessThan,
                        [V::Shared(&sum), V::Old(&limit)],
                    );
                    let refuted = parent.assume_condition(false_guard, false);
                    assert_eq!(
                        refuted.decide_masked_zero(
                            V::Shared(&masked),
                            V::Shared(&zero),
                            &mut Default::default()
                        ),
                        None
                    );
                }
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                // The reference path is an explicit test export, after the
                // shared no-export assertion above.
                let native = KernelTermExport::machine(&masked).unwrap();
                assert_eq!(
                    context.decide_masked_zero(
                        V::Old(&native),
                        V::Old(&OldMachineTerm::uint64_constant(0)),
                        &mut Default::default()
                    ),
                    Some(true)
                );
            }
        }
    }

    #[test]
    fn fresh_word_equalities_match_native_proofs_refutations_and_unknowns() {
        let mut leaked = Vec::new();
        for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            for case in 0..16 {
                let _session = crate::kernel::VerificationSession::enter();
                let variable =
                    |id| KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
                let x = variable(981001);
                let y = variable(981002);
                let z = variable(981003);
                let add = |a, b| KernelTerm::machine_binary_shared(ty, Op::Add, [a, b]);
                let mul = |a, b| KernelTerm::machine_binary_shared(ty, Op::Multiply, [a, b]);
                let literal = |value| {
                    crate::kernel::KernelTermImport::default()
                        .machine(ty, &OldMachineTerm::constant_at32(ty, value))
                };
                let observe = |root: &KernelTerm| {
                    IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap(),
                    )
                };
                let mut sources = Vec::new();
                let product = mul(x.clone(), y.clone());
                let (left, right, expected) = match case {
                    0 => (product.clone(), mul(y.clone(), z.clone()), None),
                    1 => (product.clone(), product.clone(), Some(true)),
                    2 => (
                        add(x.clone(), y.clone()),
                        add(y.clone(), x.clone()),
                        Some(true),
                    ),
                    3 => (
                        add(add(x.clone(), y.clone()), z.clone()),
                        add(x.clone(), add(y.clone(), z.clone())),
                        Some(true),
                    ),
                    4 => (
                        add(product.clone(), literal(1)),
                        product.clone(),
                        Some(false),
                    ),
                    5 => (
                        add(product.clone(), literal(1)),
                        add(product.clone(), literal(2)),
                        Some(false),
                    ),
                    6 => {
                        sources.push(Proposition::condition_is(
                            OldConditionTerm::integer_less_equal(observe(&product), observe(&z)),
                            true,
                        ));
                        sources.push(Proposition::condition_is(
                            OldConditionTerm::integer_greater_equal(observe(&product), observe(&z)),
                            true,
                        ));
                        (product.clone(), z.clone(), Some(true))
                    }
                    7 => {
                        sources.push(Proposition::condition_is(
                            OldConditionTerm::integer_less_than(observe(&product), observe(&z)),
                            true,
                        ));
                        (product.clone(), z.clone(), Some(false))
                    }
                    8 => {
                        sources.push(Proposition::condition_is(
                            OldConditionTerm::integer_equal(observe(&x), observe(&y)),
                            true,
                        ));
                        (
                            add(x.clone(), z.clone()),
                            add(y.clone(), z.clone()),
                            Some(true),
                        )
                    }
                    9 => {
                        sources.push(Proposition::condition_is(
                            OldConditionTerm::integer_less_equal(observe(&product), observe(&z)),
                            false,
                        ));
                        (product.clone(), z.clone(), Some(false))
                    }
                    10..=12 => {
                        let value = OldMachineTerm::logical_machine_binary(
                            ty,
                            Op::Multiply,
                            OldMachineTerm::Variable(Variable(981001)),
                            OldMachineTerm::Variable(Variable(981002)),
                        );
                        let width = if case == 12 { 8 } else { 4 };
                        sources.push(Proposition::condition_is(
                            OldConditionTerm::address_offset_equal(
                                AddressOffset::scale_int32(value, width),
                                AddressOffset::scale_int32(
                                    OldMachineTerm::Variable(Variable(981003)),
                                    width,
                                ),
                            ),
                            case != 10,
                        ));
                        (product.clone(), z.clone(), Some(case != 10))
                    }
                    13 => {
                        sources.push(Proposition::condition_is(
                            OldConditionTerm::signed_greater_equal(
                                OldMachineTerm::Variable(Variable(981001)),
                                OldMachineTerm::constant(3),
                            ),
                            true,
                        ));
                        sources.push(Proposition::condition_is(
                            OldConditionTerm::signed_less_equal(
                                OldMachineTerm::Variable(Variable(981001)),
                                OldMachineTerm::constant(5),
                            ),
                            true,
                        ));
                        for value in [3, 4] {
                            sources.push(Proposition::condition_is(
                                OldConditionTerm::equal(
                                    OldMachineTerm::Variable(Variable(981001)),
                                    OldMachineTerm::constant(value),
                                ),
                                false,
                            ));
                        }
                        (x.clone(), literal(5), Some(true))
                    }
                    14 | 15 => {
                        let bound = if case == 14 {
                            OldConditionTerm::integer_less_equal(observe(&product), observe(&z))
                        } else {
                            OldConditionTerm::integer_greater_equal(observe(&product), observe(&z))
                        };
                        sources.push(Proposition::condition_is(bound, true));
                        (product.clone(), z.clone(), None)
                    }
                    _ => unreachable!(),
                };
                // Both signedness readings retain observed order sources in
                // the cached graph. Opposite bounds imply equality; a strict
                // bound refutes it. One non-strict bound alone stays unknown.
                let goal = OldConditionTerm::integer_equal(observe(&left), observe(&right));
                let exports = KernelTermExport::machine_export_count();
                let context = sources
                    .iter()
                    .fold(PureFactContext::new(), |context, source| {
                        context.assume_proposition(source.clone())
                    });
                let actual = context.decide(&goal);
                let exported = KernelTermExport::machine_export_count() - exports;
                if exported != 0 {
                    leaked.push((ty, case, exported));
                }
                // Export only after checking the fresh shared input. A native
                // first run would populate the compatibility cache and hide
                // a conversion in the shared decision route.
                let native = OldConditionTerm::machine_compare(
                    ty,
                    CompareRelation::Equal,
                    KernelTermExport::machine(&left).unwrap(),
                    KernelTermExport::machine(&right).unwrap(),
                );
                assert_eq!(actual, expected, "shared {ty:?}, case {case}");
                assert_eq!(
                    context.decide(&native),
                    expected,
                    "native {ty:?}, case {case}"
                );
            }
        }
        assert!(leaked.is_empty(), "shared equality exports: {leaked:?}");
    }
    #[test]
    fn offset_equality_sources_do_not_leak_to_sibling_contexts() {
        for truth in [false, true] {
            for width in [0, 4, 8] {
                let _session = crate::kernel::VerificationSession::enter();
                let ty = MachineIntegerType::Int32;
                let x =
                    KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(983001));
                let y =
                    KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(983002));
                let z =
                    KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(983003));
                let product = KernelTerm::machine_binary_shared(ty, Op::Multiply, [x, y]);
                let native_product = OldMachineTerm::logical_machine_binary(
                    ty,
                    Op::Multiply,
                    OldMachineTerm::Variable(Variable(983001)),
                    OldMachineTerm::Variable(Variable(983002)),
                );
                let offset = |value| AddressOffset::scaled_int32_node(value, width);
                let source = Proposition::condition_is(
                    OldConditionTerm::address_offset_equal(
                        offset(native_product),
                        offset(OldMachineTerm::Variable(Variable(983003))),
                    ),
                    truth,
                );
                let observed = |root| {
                    IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap())
                };
                let goal =
                    OldConditionTerm::integer_equal(observed(product.clone()), observed(z.clone()));
                let empty = PureFactContext::new();
                let branch = empty.clone().assume_proposition(source.clone());
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(empty.decide(&goal), None);
                // A zero stride contains no information about the indices.
                // Its false equation is contradictory, not an index disequality.
                if width != 0 || truth {
                    let expected = (width == 4 || (width == 8 && truth)).then_some(truth);
                    assert_eq!(
                        branch.decide(&goal),
                        expected,
                        "width={width}, truth={truth}"
                    );
                }
                assert_eq!(empty.decide(&goal), None);
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                if width != 0 || truth {
                    let native = OldConditionTerm::equal(
                        KernelTermExport::machine(&product).unwrap(),
                        KernelTermExport::machine(&z).unwrap(),
                    );
                    assert_eq!(branch.decide(&goal), branch.decide(&native));
                }
            }
        }
    }

    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/decision/shared_equality_dispatch_tests.rs"
        );
    }
}

#[cfg(test)]
mod intrinsic_context_tests {
    use super::*;

    #[test]
    fn intrinsic_queries_never_inherit_context_hypotheses() {
        let _session = crate::kernel::VerificationSession::enter();
        let goal = OldConditionTerm::equal(
            OldMachineTerm::Variable(Variable(986001)),
            OldMachineTerm::Variable(Variable(986002)),
        );
        for truth in [true, false] {
            let context = PureFactContext::new().assume_condition(goal.clone(), truth);
            assert_eq!(context.decide(&goal), Some(truth));
            assert_eq!(PureFactContext::decide_intrinsically(&goal), None);
        }
    }

    #[test]
    fn intrinsic_read_definitions_follow_growth_restore_and_new_sessions() {
        use crate::kernel::{Address, SymbolicMemory, VerificationSession, intern_memory};
        let check = || {
            let memory = intern_memory(SymbolicMemory::new().with_block("intrinsic", 16));
            let address = Address::symbolic(Variable(986010));
            let value = Address::symbolic(Variable(986011));
            let application = Address::loaded_value(&memory, &address);
            let goal =
                OldConditionTerm::AddressEqual(Box::new(value.clone()), Box::new(application));
            assert_eq!(PureFactContext::decide_intrinsically(&goal), None);
            let before = VerificationSession::capture_state();
            let producer = PureFactContext::new();
            producer
                .equality_graph
                .register_pointer_read_definition(&value, &memory, &address);
            assert_eq!(PureFactContext::decide_intrinsically(&goal), Some(true));
            assert!(VerificationSession::restore_state(&before));
            assert_eq!(PureFactContext::decide_intrinsically(&goal), None);
        };
        for _ in 0..2 {
            let _session = VerificationSession::enter();
            check();
        }
    }
}

#[cfg(test)]
mod shared_singleton_bound_evidence_tests {
    use super::*;

    #[test]
    fn singleton_evidence_keeps_shared_bound_sources_and_requires_their_pins() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let root = KernelTerm::machine_binary_shared(
            format,
            MachineBinaryOp::Multiply,
            [
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(994001)),
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(994002)),
            ],
        );
        let observation = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
        let product = IntegerTerm::Machine(observation.clone());
        let x = OldMachineTerm::Variable(Variable(994003));
        let named = IntegerTerm::from_machine(format, x.clone()).unwrap();
        let lower = Proposition::condition_is(
            OldConditionTerm::integer_less_equal(product.clone(), named.clone()),
            true,
        );
        let upper = Proposition::condition_is(
            OldConditionTerm::integer_less_equal(named, product.clone()),
            true,
        );
        let pin = Proposition::condition_is(
            OldConditionTerm::integer_equal(product, IntegerTerm::constant_i64(7)),
            true,
        );
        let exports = KernelTermExport::machine_export_count();
        let facts = PureFactContext::new()
            .assume_proposition(lower.clone())
            .assume_proposition(upper.clone())
            .assume_proposition(pin.clone());
        let native_product = OldMachineTerm::Binary {
            format,
            op: MachineBinaryOp::Multiply,
            left: Box::new(OldMachineTerm::Variable(Variable(994001))),
            right: Box::new(OldMachineTerm::Variable(Variable(994002))),
        };
        for (source, native_left, native_right) in
            [(&lower, &native_product, &x), (&upper, &x, &native_product)]
        {
            let Proposition::ConditionIs(condition, truth) = source else {
                unreachable!()
            };
            // Keep the graph-only route's admission boundary: a held fact
            // can be available to other indexes without being a graph edge.
            // This query migration must preserve the native answer either way.
            assert_eq!(
                facts.proves_condition_from_derived_order_facts(condition.old_form(), *truth),
                facts.difference_graph_proves_order(native_left, native_right, false)
            );
            assert!(
                !PureFactContext::new()
                    .proves_condition_from_derived_order_facts(condition.old_form(), *truth)
            );
        }
        let (value, evidence) = facts
            .signed_constant_evidence(&x)
            .expect("two pinned bounds");
        assert_eq!(value, 7);
        assert!(matches!(
            evidence,
            SignedConstantEvidence::SingletonBounds { .. }
        ));
        let certificate = DirectBitvectorEqualityEvidence::EqualSignedConstants {
            value,
            left: evidence,
            right: SignedConstantEvidence::Constant,
        };
        let seven = OldMachineTerm::constant(7);
        assert!(certificate.checks(&x, &seven, &facts));
        for premises in [
            vec![lower.clone(), upper.clone()],
            vec![lower, pin.clone()],
            vec![upper, pin],
        ] {
            let incomplete = premises
                .into_iter()
                .fold(PureFactContext::new(), |facts, premise| {
                    facts.assume_proposition(premise)
                });
            assert!(!certificate.checks(&x, &seven, &incomplete));
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!observation.has_boxed_operand());
    }
}

#[cfg(test)]
mod wide_observation_tag_regression {
    use super::*;
    use crate::kernel::{IntegerTerm, KernelTermImport, SharedMachineIntegerTerm};

    #[test]
    fn wide_observation_keeps_tagged_address_equality_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let x = OldMachineTerm::Variable(Variable(993801));
        let one = OldMachineTerm::uint64_constant(1);
        let next = OldMachineTerm::uint64_add(x.clone(), one.clone());
        let tagged = OldMachineTerm::uint64_add(
            OldMachineTerm::integer_address(Address::symbolic(Variable(993803))),
            one,
        );
        let observed = |value: &OldMachineTerm| {
            IntegerTerm::Machine(
                SharedMachineIntegerTerm::from_shared(
                    format,
                    KernelTermImport::default()
                        .machine_arithmetic(format, value)
                        .unwrap(),
                )
                .unwrap(),
            )
        };
        let source =
            Proposition::condition_is(OldConditionTerm::uint64_equal(x.clone(), tagged), true);
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_proposition(source.clone());
        let goal = OldConditionTerm::integer_equal(observed(&x), observed(&next));
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        assert_eq!(branch.decide(&goal), Some(false));
        assert_eq!(
            branch.decide(&OldConditionTerm::integer_not_equal(
                observed(&x),
                observed(&next)
            )),
            Some(true)
        );
        assert_eq!(parent.decide(&goal), None);
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }
}

#[cfg(test)]
mod shared_offset_evidence_tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, SharedMachineIntegerTerm,
    };

    fn offset(term: &OldMachineTerm, width: i64) -> AddressOffset {
        let root = KernelTerm::retained_machine_operand(
            MachineIntegerType::Int32,
            MachineOperandView::Old(term),
        );
        AddressOffset::int32_scaled(
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap(),
            width,
        )
    }

    #[test]
    fn non_machine_equalities_do_not_register_offset_dependencies() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = PureFactContext::new();
        let source = OldConditionTerm::IntegerEqual(
            crate::kernel::IntegerTerm::Variable(Variable(1008150)).into(),
            crate::kernel::IntegerTerm::Variable(Variable(1008151)).into(),
        );
        facts
            .equality_graph
            .adjust_scalar_evidence_input(&source, true);
        assert!(
            facts
                .equality_graph
                .admitted
                .scalar_evidence_keys
                .is_empty()
        );
        assert!(facts.equality_graph.admitted.scalar_dependencies.is_empty());
    }

    #[test]
    fn shared_offset_evidence_preserves_native_sources() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = OldMachineTerm::Variable(Variable(1008100));
        let y = OldMachineTerm::Variable(Variable(1008101));
        let z = OldMachineTerm::Variable(Variable(1008102));
        let a = OldMachineTerm::add(x.clone(), z.clone());
        let b = OldMachineTerm::add(y.clone(), z);
        let cases = [
            vec![(OldConditionTerm::equal(a.clone(), b.clone()), true)],
            vec![
                (
                    OldConditionTerm::equal(x.clone(), OldMachineTerm::constant(3)),
                    true,
                ),
                (
                    OldConditionTerm::equal(y.clone(), OldMachineTerm::constant(3)),
                    true,
                ),
            ],
            vec![
                (
                    OldConditionTerm::signed_less_equal(x.clone(), y.clone()),
                    true,
                ),
                (
                    OldConditionTerm::signed_less_than(x.clone(), y.clone()),
                    false,
                ),
            ],
            vec![
                (
                    OldConditionTerm::signed_greater_equal(x.clone(), y.clone()),
                    true,
                ),
                (
                    OldConditionTerm::signed_greater_than(x.clone(), y.clone()),
                    false,
                ),
            ],
        ];
        for sources in cases {
            let mut facts = PureFactContext::new();
            for (source, truth) in &sources {
                facts = facts.assume_condition(source.clone(), *truth);
            }
            let left = offset(&a, 4);
            let right = offset(&b, 4);
            let exports = KernelTermExport::machine_export_count();
            let evidence = facts
                .pointer_offset_congruence_evidence(&left, &right)
                .expect("original source rule");
            assert!(evidence.checks(&left, &right, &facts));
            let rest = sources[1..]
                .iter()
                .fold(PureFactContext::new(), |rest, (source, truth)| {
                    rest.assume_condition(source.clone(), *truth)
                });
            assert!(!evidence.checks(&left, &right, &rest));
            assert!(
                facts
                    .pointer_offset_congruence_evidence(&left, &offset(&b, 8))
                    .is_none()
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn shared_offset_evidence_keeps_read_states_and_shared_premises() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = crate::kernel::SymbolicMemory::global_pointer("offset-evidence");
        let memory = crate::kernel::SymbolicMemory::new().with_block("offset-evidence", 4);
        let read = |memory| {
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                pointer.clone(),
                crate::kernel::LoadKind::Int32,
            )
        };
        let old = read(memory.clone());
        let new = read(memory.store(
            pointer.clone(),
            crate::kernel::ProgramValue::Int32(OldMachineTerm::constant(7)),
        ));
        let value = OldMachineTerm::Variable(Variable(1008130));
        let (left, right, changed) = (offset(&old, 4), offset(&value, 4), offset(&new, 4));
        let fact = OldConditionTerm::IntegerEqual(
            crate::kernel::IntegerTerm::Machine(
                left.int32_scaled_linear_form().unwrap().0[0].0.clone(),
            )
            .into(),
            crate::kernel::IntegerTerm::Machine(
                right.int32_scaled_linear_form().unwrap().0[0].0.clone(),
            )
            .into(),
        );
        let facts = PureFactContext::new().assume_condition(fact, true);
        let exports = KernelTermExport::machine_export_count();
        let proof = facts
            .pointer_offset_congruence_evidence(&left, &right)
            .expect("selected read source");
        assert!(proof.checks(&left, &right, &facts));
        assert!(!proof.checks(&changed, &right, &facts));
        assert!(
            facts
                .pointer_offset_congruence_evidence(&changed, &right)
                .is_none()
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_element_projection_matches_native_syntax_and_wide_refusal() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = OldMachineTerm::Variable(Variable(1008110));
        let cases = [
            offset(&x, 4),
            offset(&x, -4),
            AddressOffset::raw_add(offset(&x, 4), AddressOffset::constant(8)),
            AddressOffset::constant(-12),
        ];
        for v in cases {
            for width in [0, 1, 4, 8] {
                let native = element_index_from_offset(&v, width);
                let shared = shared_element_index_from_offset(&v, width);
                assert_eq!(shared.map(|v| v.value().clone()), native);
            }
        }
        for unsigned in [false, true] {
            let wide = AddressOffset::scaled_int64_node(x.clone(), 4, unsigned);
            assert!(shared_element_index_from_offset(&wide, 4).is_none());
        }
    }

    mod scaling_tests {
        use super::*;
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/shared_offset_evidence.rs"
        );
    }
}

#[cfg(test)]
#[test]
fn float_conversion_checker_rebuild_matches_constant_evaluation() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = OldMachineTerm::Variable(Variable(999953));
    let term = OldMachineTerm::opaque_conversion("c_int32_to_float32", variable.clone());
    let empty = PureFactContext::new();
    assert_eq!(empty.simplify_bitvector_under_assumptions(&term), term);
    let facts = empty.assume_condition(
        OldConditionTerm::equal(variable, OldMachineTerm::constant(1)),
        true,
    );
    assert_eq!(
        facts.simplify_bitvector_under_assumptions(&term),
        OldMachineTerm::constant(0x3f800000)
    );
}
