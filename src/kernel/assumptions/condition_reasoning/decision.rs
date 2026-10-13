use super::*;

impl PureFactContext {
    /// Selects exact premises for two terms pinned to the same signed constant.
    /// This query reads the constant-equality index, never the connected facts
    /// of either term. The caller must still check a derivation from the result.
    pub(crate) fn indexed_constant_equality_premises(
        &self,
        proposition: &Proposition,
    ) -> Option<Vec<Proposition>> {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            proposition
        else {
            return None;
        };
        let pinned = |term: &Bitvector32Term| {
            if simp_reasoning_interrupted() {
                return None;
            }
            if let Some(value) = signed_bitvector_constant(term) {
                Some((value, None))
            } else {
                self.indexed_exact_int32_constant(term)
                    .map(|(value, source)| (value, Some(*source)))
            }
        };
        let (left_value, left_source) = pinned(left)?;
        let (right_value, right_source) = pinned(right)?;
        (left_value == right_value).then(|| left_source.into_iter().chain(right_source).collect())
    }

    pub(super) fn decide_algebraic_equality(
        &self,
        left: &AlgebraicTerm,
        right: &AlgebraicTerm,
    ) -> Option<bool> {
        self.exact_condition_value(&ConditionTerm::AlgebraicEqual(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ))
    }
    pub(in crate::kernel) fn direct_bitvector_equality_evidence(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<DirectBitvectorEqualityEvidence> {
        if let Some(evidence) = self.direct_bitvector_equality_leaf_evidence(left, right) {
            return Some(evidence);
        }
        let mut current = (left.clone(), right.clone());
        let mut reductions = Vec::new();
        loop {
            let reduced = bitvector_equality_after_additive_cancellation(&current.0, &current.1)?;
            if reduced == current {
                return None;
            }
            reductions.push(reduced.clone());
            current = reduced;
            if let Some(mut evidence) =
                self.direct_bitvector_equality_leaf_evidence(&current.0, &current.1)
            {
                for (left, right) in reductions.into_iter().rev() {
                    evidence = DirectBitvectorEqualityEvidence::AdditiveCancellation {
                        left,
                        right,
                        equality: Box::new(evidence),
                    };
                }
                return Some(evidence);
            }
        }
    }

    fn direct_bitvector_equality_leaf_evidence(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<DirectBitvectorEqualityEvidence> {
        if let Some(((left_value, left), (_right_value, right))) = self
            .signed_constant_evidence(left)
            .zip(self.signed_constant_evidence(right))
            .filter(|((left, _), (right, _))| left == right)
        {
            return Some(DirectBitvectorEqualityEvidence::EqualSignedConstants {
                value: left_value,
                left,
                right,
            });
        }
        let less_equal = Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(left.clone(), right.clone()),
            true,
        );
        let not_less_than = Proposition::ConditionIs(
            ConditionTerm::signed_less_than(left.clone(), right.clone()),
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
        let greater_equal = Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
            true,
        );
        let not_greater_than = Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(left.clone(), right.clone()),
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
        term: &Bitvector32Term,
    ) -> Option<(i64, Box<Proposition>)> {
        self.exact_constant_equalities
            .get(term)?
            .keys()
            .find_map(|condition| {
                let source = Proposition::ConditionIs(condition.clone(), true);
                let value = SignedConstantEvidence::exact_equality_value(term, &source)?;
                Some((value, Box::new(source)))
            })
    }

    fn signed_constant_evidence(
        &self,
        term: &Bitvector32Term,
    ) -> Option<(i64, SignedConstantEvidence)> {
        if let Some(value) = signed_bitvector_constant(term) {
            return Some((value, SignedConstantEvidence::Constant));
        }
        if let Some((value, source)) = self.indexed_exact_int32_constant(term) {
            return Some((value, SignedConstantEvidence::ExactEquality(source)));
        }
        let variable = bitvector_variable(term)?;
        let mut lower: Option<(i64, IndexedSignedOrderBoundEvidence)> = None;
        let mut upper: Option<(i64, IndexedSignedOrderBoundEvidence)> = None;
        for (endpoint, other, strict, forward) in self.signed_order_bound_entries(term) {
            let source = self.exact_order_bound_source(&endpoint, &other, strict, forward)?;
            let pinned = self.indexed_exact_int32_constant(&other);
            let other_value = signed_bitvector_constant(&other)
                .or_else(|| pinned.as_ref().map(|(value, _)| *value));
            let evidence = IndexedSignedOrderBoundEvidence {
                other_equality: pinned.map(|(_, source)| source),
                endpoint,
                other: other.clone(),
                strict,
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

    /// Exact source for one normalized order-index entry. Four condition
    /// spellings can encode the same signed relation; indexed lookups select
    /// among those constant-many possibilities without scanning the context.
    fn exact_order_bound_source(
        &self,
        endpoint: &Bitvector32Term,
        other: &Bitvector32Term,
        strict: bool,
        forward: bool,
    ) -> Option<Proposition> {
        let (left, right) = if forward {
            (endpoint.clone(), other.clone())
        } else {
            (other.clone(), endpoint.clone())
        };
        let candidates = if strict {
            [
                (
                    ConditionTerm::signed_less_than(left.clone(), right.clone()),
                    true,
                ),
                (
                    ConditionTerm::signed_less_equal(right.clone(), left.clone()),
                    false,
                ),
                (
                    ConditionTerm::signed_greater_than(right.clone(), left.clone()),
                    true,
                ),
                (ConditionTerm::signed_greater_equal(left, right), false),
            ]
        } else {
            [
                (
                    ConditionTerm::signed_less_than(right.clone(), left.clone()),
                    false,
                ),
                (
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                ),
                (
                    ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                    false,
                ),
                (ConditionTerm::signed_greater_equal(right, left), true),
            ]
        };
        candidates.into_iter().find_map(|(condition, value)| {
            (self.condition_facts.get(&condition) == Some(&value))
                .then_some(Proposition::ConditionIs(condition, value))
        })
    }

    pub(crate) fn singleton_constant_equality_evidence(
        &self,
        variable: Variable,
    ) -> Option<(i64, DirectBitvectorEqualityEvidence)> {
        let term = Bitvector32Term::Variable(variable);
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
    pub(crate) fn decide(&self, condition: &ConditionTerm) -> Option<bool> {
        let result = self.decide_unrecorded(condition);
        if let Some(value) = result {
            record_implicit_reasoning_provenance(
                self,
                &Proposition::ConditionIs(condition.clone(), value),
            );
        }
        result
    }

    fn decide_unrecorded(&self, condition: &ConditionTerm) -> Option<bool> {
        if simp_reasoning_interrupted() {
            return None;
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
        key: &(u64, ConditionTerm),
        condition: &ConditionTerm,
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

    fn decide_inner(&self, condition: &ConditionTerm) -> Option<bool> {
        // A comparison of a term with itself is decided by its shape, with
        // no fact: the same one-comparison rule every `using` list applies
        // (`proposition_holds_without_facts`).
        if let Some(value) = condition.reflexive_value() {
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
        if let Some(value) = self.decide_indexed_greater_equal(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_masked_order(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_widened_sum_bound(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_unsigned_order_of_nonnegative_signed(condition) {
            return Some(value);
        }
        // Wide comparisons may use a recorded constant equality. Consult only
        // the queried terms' equality components, never unrelated conditions.
        let wide_comparison = match condition {
            ConditionTerm::Bitvector64SignedLessThan(a, b) => Some((a, b, 0)),
            ConditionTerm::Bitvector64SignedLessEqual(a, b) => Some((a, b, 1)),
            ConditionTerm::Bitvector64SignedGreaterThan(a, b) => Some((a, b, 2)),
            ConditionTerm::Bitvector64SignedGreaterEqual(a, b) => Some((a, b, 3)),
            ConditionTerm::Bitvector64UnsignedLessThan(a, b) => Some((a, b, 4)),
            ConditionTerm::Bitvector64UnsignedLessEqual(a, b) => Some((a, b, 5)),
            ConditionTerm::Bitvector64UnsignedGreaterThan(a, b) => Some((a, b, 6)),
            ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b) => Some((a, b, 7)),
            ConditionTerm::Bitvector64Equal(a, b) => Some((a, b, 8)),
            _ => None,
        };
        if let Some((left, right, operator)) = wide_comparison {
            if operator == 8 {
                let left_base = self.bitvector64_identity_base(left);
                let right_base = self.bitvector64_identity_base(right);
                if (!std::ptr::eq(left_base, left.as_ref())
                    || !std::ptr::eq(right_base, right.as_ref()))
                    && let Some(answer) = self.decide(&ConditionTerm::int64_equal(
                        left_base.clone(),
                        right_base.clone(),
                    ))
                {
                    return Some(answer);
                }
            }
            let left_constant = self.wide_constant_from_equalities(left);
            let right_constant = self.wide_constant_from_equalities(right);
            // A constant outside the queried operand's signed interval cannot
            // have the same bits. Consult only that operand's indexed facts;
            // do not clone pointer or memory terms to try extra comparisons.
            if operator == 8 {
                let bounded = match (left_constant, right_constant) {
                    (None, Some(value)) => self
                        .int64_interval(left)
                        .map(|bounds| (bounds, value as i64)),
                    (Some(value), None) => self
                        .int64_interval(right)
                        .map(|bounds| (bounds, value as i64)),
                    _ => None,
                };
                if bounded.is_some_and(|((lower, upper), value)| value < lower || value > upper) {
                    return Some(false);
                }
            }
            if let (Some(left), Some(right)) = (left_constant, right_constant) {
                return Some(match operator {
                    0 => (left as i64) < (right as i64),
                    1 => (left as i64) <= (right as i64),
                    2 => (left as i64) > (right as i64),
                    3 => (left as i64) >= (right as i64),
                    4 => left < right,
                    5 => left <= right,
                    6 => left > right,
                    7 => left >= right,
                    _ => left == right,
                });
            }
            // A single constant endpoint also transports an indexed order
            // fact through an equality (e.g. i < 4, len == 4 => i < len).
            // Consult only the two equality components, and recurse only if
            // replacing a nonconstant endpoint makes the goal smaller.
            let replacement = |term: &Bitvector32Term, value: Option<u64>| {
                if term.uint64_as_const().is_some() || term.int64_as_const().is_some() {
                    term.clone()
                } else if let Some(value) = value {
                    if operator < 4 {
                        Bitvector32Term::Int64Constant(value as i64)
                    } else {
                        Bitvector32Term::UInt64Constant(value)
                    }
                } else {
                    term.clone()
                }
            };
            let a = replacement(left, left_constant);
            let b = replacement(right, right_constant);
            if &a != left.as_ref() || &b != right.as_ref() {
                let rewritten = match operator {
                    0 => ConditionTerm::int64_signed_less_than(a, b),
                    1 => ConditionTerm::int64_signed_less_equal(a, b),
                    2 => ConditionTerm::int64_signed_greater_than(a, b),
                    3 => ConditionTerm::int64_signed_greater_equal(a, b),
                    4 => ConditionTerm::uint64_less_than(a, b),
                    5 => ConditionTerm::uint64_less_equal(a, b),
                    6 => ConditionTerm::uint64_greater_than(a, b),
                    7 => ConditionTerm::uint64_greater_equal(a, b),
                    _ => ConditionTerm::uint64_equal(a, b),
                };
                if let Some(value) = self.decide(&rewritten) {
                    return Some(value);
                }
            }
        }
        match condition {
            ConditionTerm::AlgebraicEqual(left, right) => {
                self.decide_algebraic_equality(left, right)
            }
            ConditionTerm::Constant(value) => Some(*value),
            _ => {
                if let Some(value) = self.exact_condition_value(condition) {
                    return Some(value);
                }
                if let Some(value) = self.decide_exact_signed_constant_order(condition) {
                    return Some(value);
                }
                if let Some(value) = self.decide_byte_equality_from_constant_class(condition) {
                    return Some(value);
                }
                if let Some(value) = self.decide_reflexive_float_comparison(condition) {
                    return Some(value);
                }
                if let ConditionTerm::Bitvector32Equal(left, right) = condition
                    && (self.int32_values_known_equal(left, right)
                        || super::super::super::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                            left,
                            right,
                            self,
                        ))
                {
                    return Some(true);
                }
                if let ConditionTerm::Bitvector64Equal(left, right) = condition
                    && crate::kernel::memory_provenance::wide_loads_have_same_canonical_value(
                        left, right, self,
                    )
                {
                    return Some(true);
                }
                if let ConditionTerm::PointerEqual(left, right) = condition
                    && (crate::kernel::memory_provenance::pointer_read_has_stored_value(
                        left, right, self,
                    ) || crate::kernel::memory_provenance::pointer_read_has_stored_value(
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
                if let ConditionTerm::IntegerEqual(left, right) = condition
                    && super::super::super::reasoning::integer_range_fold_terms_alpha_equivalent(
                        left, right, self,
                    )
                {
                    return Some(true);
                }
                // Pointer conditions are already in their canonical structural
                // form: `simplify_condition_under_assumptions` only clones
                // them. Avoid cloning and then deeply comparing symbolic
                // pointer terms (which may embed whole memory snapshots)
                // before routing to the dedicated pointer decision rules.
                if matches!(
                    condition,
                    ConditionTerm::PointerOffsetEqual(_, _) | ConditionTerm::PointerEqual(_, _)
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
                        ConditionTerm::Constant(value) => Some(value),
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
                    .or_else(|| self.decide_from_order_facts(condition))
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
    fn decide_pointer_disequality(&self, condition: &ConditionTerm) -> Option<bool> {
        match condition {
            ConditionTerm::PointerEqual(left, right) => self
                .pointers_distinct_by_nullness(left, right)
                .or_else(|| self.pointers_distinct_by_owned_anchors(left, right)),
            ConditionTerm::PointerOffsetEqual(left, right) => self
                .offsets_distinct_by_nullness(left, right)
                .or_else(|| self.offsets_distinct_by_separation(left, right))
                .or_else(|| self.offsets_distinct_by_owned_anchors(left, right)),
            _ => None,
        }
    }

    fn pointers_distinct_by_nullness(&self, left: &Pointer, right: &Pointer) -> Option<bool> {
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
        start: &Pointer,
    ) -> Vec<(Pointer, Option<Pointer>)> {
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

    /// Records the exact equalities that connect `start` to the spelling at
    /// `index` of its component, one per hop, each taken back through the
    /// exact check. Fails when a hop is no longer an exact fact, which a
    /// derived index never allows, so the conclusion never rests on it.
    fn record_pointer_equality_path(
        &self,
        component: &[(Pointer, Option<Pointer>)],
        index: usize,
    ) -> Option<()> {
        let mut current = &component[index];
        while let Some(previous) = &current.1 {
            crate::instrumentation::record_deterministic_work(1);
            let condition = if previous.block == current.0.block {
                ConditionTerm::pointer_offset_equal(
                    previous.offset.clone(),
                    current.0.offset.clone(),
                )
            } else {
                ConditionTerm::pointer_equal(previous.clone(), current.0.clone())
            };
            if self.exact_condition_value(&condition) != Some(true) {
                return None;
            }
            current = component.iter().find(|(pointer, _)| pointer == previous)?;
        }
        Some(())
    }

    /// Two pointers differ when each, or a pointer exact equalities prove it
    /// equal to, lies inside an owned memory member of one held composition,
    /// and the two members are distinct: the composition law separates its
    /// owned members, and one address cannot lie in both. The members may
    /// lie in different blocks, which is how a symbolic identity payload and
    /// a loaded pointer are told apart once each is proved equal to the base
    /// its cells are owned under. Each member is found by the base index
    /// under the spelling's additive bases, as a store's member is. String
    /// literal storage never counts: two occurrences with identical bytes
    /// may be one object, so their ranges are deliberately never separated.
    fn pointers_distinct_by_owned_anchors(&self, left: &Pointer, right: &Pointer) -> Option<bool> {
        if self.resource_compositions.is_empty() {
            return None;
        }
        let lefts = self.pointer_equality_component(left);
        let rights = self.pointer_equality_component(right);
        if lefts
            .iter()
            .any(|(pointer, _)| rights.iter().any(|(other, _)| other == pointer))
        {
            // One equality chain connects the two sides: they are one
            // address, and no owned member can say otherwise.
            return None;
        }
        for resources in self.resource_compositions.iter() {
            for (left_index, (left_spelling, _)) in lefts.iter().enumerate() {
                let Some(left_member) =
                    self.owned_member_holding_access(resources, left_spelling, 1)
                else {
                    continue;
                };
                for (right_index, (right_spelling, _)) in rights.iter().enumerate() {
                    let Some(right_member) =
                        self.owned_member_holding_access(resources, right_spelling, 1)
                    else {
                        continue;
                    };
                    if left_member == right_member
                        || matches!(left_member.base().block, PointerBlock::StringLiteral { .. })
                        || matches!(
                            right_member.base().block,
                            PointerBlock::StringLiteral { .. }
                        )
                    {
                        continue;
                    }
                    self.record_pointer_equality_path(&lefts, left_index)?;
                    self.record_pointer_equality_path(&rights, right_index)?;
                    record_implicit_reasoning_provenance(
                        self,
                        &Proposition::CResourceComposition(resources.clone()),
                    );
                    return Some(false);
                }
            }
        }
        None
    }

    /// The same-block form of [`Self::pointers_distinct_by_owned_anchors`].
    /// The comparison names only its two offsets, so the block spellings
    /// come from the pointers of those offsets that an exact equality has
    /// aliased across blocks; two pointers of one block are equal exactly
    /// when their offsets are, so a block that tells the two offsets apart
    /// decides the comparison whatever block it came from.
    fn offsets_distinct_by_owned_anchors(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> Option<bool> {
        if left == right {
            return None;
        }
        let spellings = |offset: &PointerOffsetTerm| {
            self.pointer_block_aliases_by_offset
                .get(offset)
                .into_iter()
                .flat_map(|pointers| pointers.iter().cloned())
                .collect::<Vec<_>>()
        };
        for pointer in spellings(left) {
            let other = Pointer {
                block: pointer.block.clone(),
                offset: right.clone(),
            };
            if self.pointers_distinct_by_owned_anchors(&pointer, &other) == Some(false) {
                return Some(false);
            }
        }
        for pointer in spellings(right) {
            let other = Pointer {
                block: pointer.block.clone(),
                offset: left.clone(),
            };
            if self.pointers_distinct_by_owned_anchors(&other, &pointer) == Some(false) {
                return Some(false);
            }
        }
        None
    }

    /// Whether an exact fact settles this pointer's null-ness.
    ///
    /// The null pointer is null intrinsically, and a pointer whose block is
    /// proven distinct from the null block is not null by the same rule that
    /// decides any other block disequality.
    fn pointer_nullness(&self, pointer: &Pointer) -> Option<bool> {
        let null = Pointer::null();
        if *pointer == null {
            return Some(true);
        }
        if let Some(value) = self.exact_condition_value(&ConditionTerm::PointerEqual(
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
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
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
            let pointer_at = |offset: &PointerOffsetTerm| Pointer {
                block: block.clone(),
                offset: offset.clone(),
            };
            if self.pointer_nullness(&pointer_at(left)) == Some(*value)
                && self.pointer_nullness(&pointer_at(right)) == Some(!*value)
            {
                return Some(false);
            }
        }
        None
    }

    /// Two offsets differ when each is the address of the first element of
    /// one of two separated memory ranges: one address cannot hold an
    /// element of both.
    fn offsets_distinct_by_separation(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> Option<bool> {
        if left == right {
            return None;
        }
        let key = Self::separated_anchor_key(left.clone(), right.clone());
        if let Some(separation) = self
            .separated_anchor_offsets
            .get(&key)
            .and_then(|facts| facts.iter().next())
        {
            record_implicit_reasoning_provenance(self, separation);
            return Some(false);
        }
        // Two owned members of one composition, anchored at these offsets.
        let resources = self
            .resource_compositions
            .iter()
            .find(|resources| resources.separates_owned_anchors(left, right))?;
        record_implicit_reasoning_provenance(
            self,
            &Proposition::CResourceComposition(resources.clone()),
        );
        Some(false)
    }

    fn decide_reflexive_float_comparison(&self, condition: &ConditionTerm) -> Option<bool> {
        let (operator, left, right) = match condition {
            ConditionTerm::Float32(CFloatCondition::Comparison {
                operator,
                left,
                right,
            }) => (*operator, left.as_ref(), right.as_ref()),
            ConditionTerm::Float64(CFloatCondition::Comparison {
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
            ConditionTerm::Float32(_) => {
                ConditionTerm::float32_classification(left.clone(), CFloatClassification::Finite)
            }
            ConditionTerm::Float64(_) => {
                ConditionTerm::float64_classification(left.clone(), CFloatClassification::Finite)
            }
            _ => unreachable!(),
        };
        let finite_right = match condition {
            ConditionTerm::Float32(_) => {
                ConditionTerm::float32_classification(right.clone(), CFloatClassification::Finite)
            }
            ConditionTerm::Float64(_) => {
                ConditionTerm::float64_classification(right.clone(), CFloatClassification::Finite)
            }
            _ => unreachable!(),
        };
        let left_is_finite = self.decide(&finite_left);
        let right_is_finite = self.decide(&finite_right);
        if left_is_finite != Some(true) && right_is_finite != Some(true) {
            return None;
        }
        Some(match operator {
            CComparisonOperator::Equal
            | CComparisonOperator::LessEqual
            | CComparisonOperator::GreaterEqual => true,
            CComparisonOperator::NotEqual
            | CComparisonOperator::LessThan
            | CComparisonOperator::GreaterThan => false,
        })
    }

    pub(in crate::kernel) fn decide_intrinsically(condition: &ConditionTerm) -> Option<bool> {
        Self::new().decide(condition)
    }

    /// A byte read compared with a constant, decided by the constant its
    /// equality class carries (`ConstantClasses`). One byte has one name, so
    /// its signed and unsigned reads share that class's evidence in both
    /// directions: `int8(u) == 7` settles `u` to 7 and `u == 200` settles
    /// `int8(u)` to -56 (see `constant_classes`). The queried side must be a
    /// byte read, an unsigned byte load or the signed conversion of one, so
    /// this answers only the byte questions the index was extended for; it
    /// is one memoized class lookup, not a walk over the facts.
    fn decide_byte_equality_from_constant_class(&self, condition: &ConditionTerm) -> Option<bool> {
        let ConditionTerm::Bitvector32Equal(left, right) = condition else {
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
            Some(Bitvector32Term::MemoryLoad(_, _, LoadKind::UInt8))
        ) {
            return None;
        }
        self.signed_constant_after_equality_normalization(term)
            .map(|known| known == constant)
    }

    /// Integer strict and inclusive bounds differ by one. Keep the frozen
    /// bounded term intact and look up only the equivalent recorded bound.
    /// The signed endpoints are handled before incrementing or decrementing.
    pub(super) fn decide_exact_signed_constant_order(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        let (left, right, greater, strict) = match condition {
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) => (left, right, true, true),
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => (left, right, true, false),
            ConditionTerm::Bitvector32SignedLessThan(left, right) => (left, right, false, true),
            ConditionTerm::Bitvector32SignedLessEqual(left, right) => (left, right, false, false),
            _ => return None,
        };
        let (term, bound, greater) = if let Some(bound) = right.as_const() {
            (left.as_ref().clone(), bound as i32, greater)
        } else {
            let bound = left.as_const()?;
            (right.as_ref().clone(), bound as i32, !greater)
        };
        let shifted = if greater == strict {
            match bound.checked_add(1) {
                Some(bound) => bound,
                None => return Some(!strict),
            }
        } else {
            match bound.checked_sub(1) {
                Some(bound) => bound,
                None => return Some(!strict),
            }
        };
        let bound = Bitvector32Term::Constant(shifted as u32);
        let equivalent = match (greater, strict) {
            (true, true) => ConditionTerm::signed_greater_equal(term, bound),
            (true, false) => ConditionTerm::signed_greater_than(term, bound),
            (false, true) => ConditionTerm::signed_less_equal(term, bound),
            (false, false) => ConditionTerm::signed_less_than(term, bound),
        };
        if let Some(value) = self.exact_condition_value(&equivalent) {
            return Some(value);
        }
        // An explicitly recorded equality can name the same frozen term
        // through a load variable. Visit its indexed spellings only; an
        // unrelated open order fact is never a candidate for this rule.
        for key in self.condition_match_candidate_keys(&equivalent) {
            let Some(facts) = self.condition_facts_by_sides.get(&key) else {
                continue;
            };
            for (fact, value) in facts {
                crate::instrumentation::record_deterministic_work(1);
                if self.condition_matches(fact, &equivalent) {
                    record_implicit_reasoning_provenance(
                        self,
                        &Proposition::ConditionIs(fact.clone(), *value),
                    );
                    return Some(*value);
                }
            }
        }
        None
    }

    pub(in crate::kernel) fn has_condition_fact(
        &self,
        condition: ConditionTerm,
        value: bool,
    ) -> bool {
        // The fact itself, by key; then the facts filed under the keys this
        // query's sides spell, directly or through their recorded-equality
        // classes, each confirmed by `condition_matches`.
        let matched = if self.condition_facts.get(&condition) == Some(&value) {
            Some(Proposition::ConditionIs(condition.clone(), value))
        } else {
            self.condition_match_candidate_keys(&condition)
                .into_iter()
                .find_map(|key| {
                    self.condition_facts_by_sides
                        .get(&key)?
                        .iter()
                        .find(|(fact, fact_value)| {
                            crate::instrumentation::record_deterministic_work(1);
                            crate::kernel::assumptions::count_condition_fact_visit();
                            **fact_value == value && self.condition_matches(fact, &condition)
                        })
                        .map(|(fact, fact_value)| {
                            Proposition::ConditionIs(fact.clone(), *fact_value)
                        })
                })
                .or_else(|| {
                    let family =
                        crate::kernel::assumptions::condition_match_key(&condition)?.family();
                    self.open_condition_facts
                        .get(&family)?
                        .iter()
                        .find(|(fact, fact_value)| {
                            crate::instrumentation::record_deterministic_work(1);
                            crate::kernel::assumptions::count_condition_fact_visit();
                            **fact_value == value && self.condition_matches(fact, &condition)
                        })
                        .map(|(fact, fact_value)| {
                            Proposition::ConditionIs(fact.clone(), *fact_value)
                        })
                })
        };
        if let Some(proposition) = matched {
            record_implicit_reasoning_provenance(self, &proposition);
            true
        } else {
            false
        }
    }

    /// The `condition_facts_by_sides` keys a fact matching `condition`
    /// can be filed under: the query's own key, and the keys its sides'
    /// recorded-equality classes spell. The classes are what
    /// `condition_matches` relates through equality facts; each side's class
    /// is read once from the indexed equality graph.
    fn condition_match_candidate_keys(
        &self,
        condition: &ConditionTerm,
    ) -> Vec<crate::kernel::primitives::ConditionMatchKey> {
        use crate::kernel::primitives::ConditionMatchKey;
        let Some(key) = crate::kernel::assumptions::condition_match_key(condition) else {
            return Vec::new();
        };
        let spellings = |term: &Bitvector32Term| {
            let mut terms = vec![term.clone()];
            terms.extend(self.bitvector_equality_class(term));
            terms
        };
        let mut keys = BTreeSet::from([key.clone()]);
        match &key {
            ConditionMatchKey::Equal(left, right) => {
                for left in spellings(left) {
                    for right in spellings(right) {
                        keys.insert(if left <= right {
                            ConditionMatchKey::Equal(left.clone(), right)
                        } else {
                            ConditionMatchKey::Equal(right, left.clone())
                        });
                    }
                }
            }
            ConditionMatchKey::Order(strict, lower, upper) => {
                for lower in spellings(lower) {
                    for upper in spellings(upper) {
                        keys.insert(ConditionMatchKey::Order(*strict, lower.clone(), upper));
                    }
                }
            }
            ConditionMatchKey::OverflowAdd(left, right) => {
                for left in spellings(left) {
                    for right in spellings(right) {
                        keys.insert(if left <= right {
                            ConditionMatchKey::OverflowAdd(left.clone(), right)
                        } else {
                            ConditionMatchKey::OverflowAdd(right, left.clone())
                        });
                    }
                }
            }
            ConditionMatchKey::OffsetEqual(_, _) => {}
        }
        keys.into_iter().collect()
    }

    /// The exact recorded value of `condition` (or of its mirrored form),
    /// recording the fact as consumed provenance when a collection is
    /// active: an exact lookup is a premise like any other.
    pub(in crate::kernel) fn exact_condition_value(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        let value = self.exact_condition_value_unrecorded(condition);
        if let Some(value) = value {
            record_implicit_reasoning_provenance(
                self,
                &Proposition::ConditionIs(condition.clone(), value),
            );
        }
        value
    }

    fn exact_condition_value_unrecorded(&self, condition: &ConditionTerm) -> Option<bool> {
        self.condition_facts
            .get(condition)
            .copied()
            .or_else(|| match condition {
                ConditionTerm::Bitvector32Equal(left, right) => self
                    .condition_facts
                    .get(&ConditionTerm::equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied(),
                ConditionTerm::PointerOffsetEqual(left, right) => self
                    .condition_facts
                    .get(&ConditionTerm::pointer_offset_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied(),
                ConditionTerm::PointerEqual(left, right) => self
                    .condition_facts
                    .get(&ConditionTerm::pointer_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied(),
                ConditionTerm::Bitvector32SignedLessThan(left, right) => self
                    .condition_facts
                    .get(&ConditionTerm::signed_greater_than(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied()
                    .or_else(|| {
                        self.condition_facts
                            .get(&ConditionTerm::signed_greater_equal(
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                            ))
                            .map(|value| !value)
                    }),
                ConditionTerm::Bitvector32SignedLessEqual(left, right) => self
                    .condition_facts
                    .get(&ConditionTerm::signed_greater_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied()
                    .or_else(|| {
                        self.condition_facts
                            .get(&ConditionTerm::signed_greater_than(
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                            ))
                            .map(|value| !value)
                    }),
                ConditionTerm::Bitvector32SignedGreaterThan(left, right) => self
                    .condition_facts
                    .get(&ConditionTerm::signed_less_than(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied()
                    .or_else(|| {
                        self.condition_facts
                            .get(&ConditionTerm::signed_less_equal(
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                            ))
                            .map(|value| !value)
                    }),
                ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => self
                    .condition_facts
                    .get(&ConditionTerm::signed_less_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ))
                    .copied()
                    .or_else(|| {
                        self.condition_facts
                            .get(&ConditionTerm::signed_less_than(
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                            ))
                            .map(|value| !value)
                    }),
                _ => None,
            })
    }

    pub(in crate::kernel) fn decide_bitvector_equality_shallow(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        if self.int32_values_known_equal(left, right) {
            return Some(true);
        }
        if let Some(value) =
            self.exact_condition_value(&ConditionTerm::equal(left.clone(), right.clone()))
        {
            return Some(value);
        }
        // Purely structural arithmetic: terms whose affine difference is a
        // constant that is nonzero mod 2^32 are unequal in every model
        // (x + c wraps back to x only when c is a multiple of 2^32). No
        // facts are consulted, so the verdict is identical in smart
        // execution and pinned check.
        if let Some(difference) = affine_bitvector_difference_constant(left, right)
            && difference.rem_euclid(1i64 << 32) != 0
        {
            return Some(false);
        }
        match (
            self.bitvector_constant_from_direct_equalities(left),
            self.bitvector_constant_from_direct_equalities(right),
        ) {
            (Some(left), Some(right)) => Some(left == right),
            _ => None,
        }
    }

    pub(in crate::kernel) fn bitvector_constant_from_direct_equalities(
        &self,
        term: &Bitvector32Term,
    ) -> Option<u32> {
        if let Some(value) = term.as_const() {
            return Some(value);
        }
        // Every literal reached by a true equality settles its constant
        // class. An unknown class therefore needs no adjacency walk. This
        // is only a negative shortcut: folded class values must not broaden
        // the exact-equality judgment below.
        if matches!(
            self.constant_classes.class_constant(term),
            None | Some(SignedConstantResolution::Unknown)
        ) {
            return None;
        }
        let mut pending = vec![term.clone()];
        let mut visited = BTreeSet::new();
        while let Some(current) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if !visited.insert(current.clone()) {
                continue;
            }
            if let Some(value) = current.as_const() {
                return Some(value);
            }
            if let Some(neighbors) = self.direct_bitvector_equalities.get(&current) {
                for (_, other) in neighbors.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    count_condition_fact_visit();
                    pending.push(other.clone());
                }
            }
        }
        None
    }

    /// Strip bit-preserving 64-bit conversions and signed additive identities
    /// through borrowed operands. Each node costs at most its operand's indexed
    /// query; clone only after the walk, not each remaining subtree.
    fn bitvector64_identity_base<'a>(&self, mut term: &'a Bitvector32Term) -> &'a Bitvector32Term {
        loop {
            term = match term {
                Bitvector32Term::Int64Add(a, b)
                    if self.wide_constant_from_equalities(b) == Some(0) =>
                {
                    a
                }
                Bitvector32Term::Int64Add(a, b)
                    if self.wide_constant_from_equalities(a) == Some(0) =>
                {
                    b
                }
                Bitvector32Term::Int64Subtract(a, b)
                    if self.wide_constant_from_equalities(b) == Some(0) =>
                {
                    a
                }
                // A signed-to-unsigned 64-bit conversion preserves all bits.
                Bitvector32Term::UInt64FromInt64(value) => value,
                _ => return term,
            };
        }
    }

    pub(in crate::kernel) fn wide_constant_from_equalities(
        &self,
        term: &Bitvector32Term,
    ) -> Option<u64> {
        fn evaluate(
            context: &PureFactContext,
            term: &Bitvector32Term,
            active: &mut BTreeSet<usize>,
            memo: &mut BTreeMap<usize, Option<u64>>,
        ) -> Option<u64> {
            // Identities live only for this query. No deep term clone or
            // structural comparison is needed for the traversal memo.
            let identity = term as *const Bitvector32Term as usize;
            if let Some(value) = memo.get(&identity) {
                return *value;
            }
            // Equality cycles and deeply nested arithmetic are search, not
            // permission to grow the native stack without a bound.
            if active.len() >= 128 {
                return None;
            }
            if !active.insert(identity) {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            let mut value = match term {
                Bitvector32Term::UInt64Constant(value) => Some(*value),
                Bitvector32Term::Int64Constant(value) => Some(*value as u64),
                Bitvector32Term::Int64Add(left, right)
                | Bitvector32Term::Int64Subtract(left, right)
                | Bitvector32Term::Int64Multiply(left, right)
                | Bitvector32Term::Int64Divide(left, right)
                | Bitvector32Term::Int64Remainder(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .and_then(|(a, b)| {
                            let (a, b) = (a as i64, b as i64);
                            match term {
                                Bitvector32Term::Int64Add(..) => a.checked_add(b),
                                Bitvector32Term::Int64Subtract(..) => a.checked_sub(b),
                                Bitvector32Term::Int64Multiply(..) => a.checked_mul(b),
                                Bitvector32Term::Int64Divide(..) => a.checked_div(b),
                                _ => a.checked_rem(b),
                            }
                            .map(|value| value as u64)
                        })
                }
                Bitvector32Term::Int64From32(inner) | Bitvector32Term::Int64FromUInt32(inner) => {
                    context
                        .known_signed_constant_after_normalization(inner)
                        .map(|a| {
                            if matches!(term, Bitvector32Term::Int64From32(..)) {
                                a as i32 as i64 as u64
                            } else {
                                u64::from(a as u32)
                            }
                        })
                }
                Bitvector32Term::UInt64Add(left, right) => evaluate(context, left, active, memo)
                    .zip(evaluate(context, right, active, memo))
                    .map(|(a, b)| a.wrapping_add(b)),
                Bitvector32Term::UInt64Subtract(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .map(|(a, b)| a.wrapping_sub(b))
                }
                Bitvector32Term::UInt64Multiply(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .map(|(a, b)| a.wrapping_mul(b))
                }
                Bitvector32Term::UInt64Divide(left, right)
                | Bitvector32Term::UInt64Remainder(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .and_then(|(a, b)| {
                            if b == 0 {
                                return None;
                            }
                            Some(if matches!(term, Bitvector32Term::UInt64Divide(..)) {
                                a / b
                            } else {
                                a % b
                            })
                        })
                }
                Bitvector32Term::UInt64BitwiseAnd(left, right)
                | Bitvector32Term::UInt64BitwiseOr(left, right)
                | Bitvector32Term::UInt64BitwiseXor(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .map(|(a, b)| match term {
                            Bitvector32Term::UInt64BitwiseAnd(..) => a & b,
                            Bitvector32Term::UInt64BitwiseOr(..) => a | b,
                            _ => a ^ b,
                        })
                }
                Bitvector32Term::UInt64BitwiseNot(inner) => {
                    evaluate(context, inner, active, memo).map(|a| !a)
                }
                Bitvector32Term::UInt64ShiftLeft(left, right)
                | Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
                    let count = context
                        .known_signed_constant_after_normalization(right)
                        .map(|a| u64::from(a as u32))
                        .or_else(|| evaluate(context, right, active, memo));
                    evaluate(context, left, active, memo)
                        .zip(count)
                        .and_then(|(a, b)| {
                            if b >= 64 {
                                return None;
                            }
                            Some(if matches!(term, Bitvector32Term::UInt64ShiftLeft(..)) {
                                a.wrapping_shl(b as u32)
                            } else {
                                a >> b
                            })
                        })
                }
                Bitvector32Term::UInt64From32(inner) | Bitvector32Term::UInt64FromInt32(inner) => {
                    context
                        .known_signed_constant_after_normalization(inner)
                        .map(|a| {
                            if matches!(term, Bitvector32Term::UInt64FromInt32(..)) {
                                a as i32 as i64 as u64
                            } else {
                                u64::from(a as u32)
                            }
                        })
                }
                Bitvector32Term::UInt64FromInt64(inner) => evaluate(context, inner, active, memo),
                Bitvector32Term::UInt32From64(inner) => {
                    evaluate(context, inner, active, memo).map(|a| u64::from(a as u32))
                }
                _ => None,
            };
            if value.is_none()
                && let Some(neighbors) = context.bitvector64_equality_facts.get(term)
            {
                for (equal, fact) in neighbors.iter() {
                    value = evaluate(context, equal, active, memo);
                    if value.is_some() {
                        record_implicit_reasoning_provenance(
                            context,
                            &Proposition::ConditionIs(fact.clone(), true),
                        );
                        break;
                    }
                }
            }
            active.remove(&identity);
            memo.insert(identity, value);
            value
        }
        evaluate(self, term, &mut BTreeSet::new(), &mut BTreeMap::new())
    }

    /// Query wrapping int32 value equality maintained by the trusted graph.
    /// This performs no fact-component walk, arithmetic search, or snapshot
    /// transport. `false` means unknown. Equal residues establish exact byte
    /// offsets only through the separate offset judgment's no-wrap guards.
    pub(in crate::kernel) fn int32_values_known_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right || self.equality_graph.are_int32_equal(left, right)
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
    pub(in crate::kernel) fn bitvector_equality_class(
        &self,
        term: &Bitvector32Term,
    ) -> Vec<Bitvector32Term> {
        let equality_index = self.bitvector_equality_index();
        if equality_index.is_empty() {
            return Vec::new();
        }
        let start = equality_graph_term_key(term);
        if !equality_index.contains_key(&start) {
            return Vec::new();
        }
        let mut seen = BTreeSet::from([start.clone()]);
        let mut stack = vec![start.clone()];
        while let Some(current) = stack.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(neighbors) = equality_index.get(&current) {
                for neighbor in neighbors.keys() {
                    if seen.insert(neighbor.clone()) {
                        stack.push(neighbor.clone());
                    }
                }
            }
        }
        seen.remove(&start);
        seen.remove(term);
        seen.into_iter().collect()
    }

    /// Retain one deterministic path made only from exact int32 equality
    /// conditions. Memory-canonicalized and pointer-offset-derived graph
    /// edges deliberately remain for their own typed evidence kinds.
    pub(in crate::kernel) fn exact_bitvector_equality_path_evidence(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<Vec<BitvectorEqualityDerivationStep>> {
        if left == right
            || equality_graph_term_key(left) != *left
            || equality_graph_term_key(right) != *right
        {
            return None;
        }
        let equality_index = self.bitvector_equality_index();
        let mut seen = BTreeSet::new();
        let mut stack = vec![(left.clone(), Vec::new())];
        while let Some((current, path)) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            if current == *right && !path.is_empty() {
                return Some(path);
            }
            let Some(neighbors) = equality_index.get(&current) else {
                continue;
            };
            for (neighbor, premise) in neighbors.iter().rev() {
                let Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(premise_left, premise_right),
                    true,
                ) = premise
                else {
                    continue;
                };
                if equality_graph_term_key(premise_left) != **premise_left
                    || equality_graph_term_key(premise_right) != **premise_right
                {
                    continue;
                }
                let mut extended = path.clone();
                extended.push(BitvectorEqualityDerivationStep {
                    source: current.clone(),
                    target: neighbor.clone(),
                    premise: premise.clone(),
                });
                stack.push((neighbor.clone(), extended));
            }
        }
        None
    }

    fn pointer_read_snapshot_scaled_evidence(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        byte_width: i64,
    ) -> Option<PointerOffsetCongruenceEvidence> {
        if matches!(
            crate::kernel::eval::viewed_as_memory_load(left),
            Some(Bitvector32Term::MemoryLoad(_, _, LoadKind::Pointer))
        ) && matches!(
            crate::kernel::eval::viewed_as_memory_load(right),
            Some(Bitvector32Term::MemoryLoad(_, _, LoadKind::Pointer))
        ) {
            let capture =
                crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start_active();
            let equal = crate::kernel::memory_provenance::checked_recorded_atomic_load_equality(
                left, right, self,
            ) || crate::kernel::memory_provenance::checked_origin_load_equality(
                left, right, self,
            );
            let mut witnesses = capture.finish();
            if equal && witnesses.len() == 1 {
                let equality = witnesses.pop()?;
                if equality.checks_exact_pointer_read_terms(left, right, self) {
                    return Some(PointerOffsetCongruenceEvidence::PointerReadSnapshot {
                        byte_width,
                        equality: Box::new(equality),
                    });
                }
            }
        }
        for (read, other, reversed) in [(left, right, false), (right, left, true)] {
            let Some(Bitvector32Term::MemoryLoad(_, address, LoadKind::Pointer)) =
                crate::kernel::eval::viewed_as_memory_load(read)
            else {
                continue;
            };
            let other_offset = PointerOffsetTerm::scale_int32(other.clone(), byte_width);
            // Only aliases of the selected target offset, never an ambient
            // fact scan. The existing direct path search uses this same bound.
            for intermediate in self
                .pointer_offset_aliases
                .get(&other_offset)
                .into_iter()
                .flat_map(|aliases| aliases.iter())
                .take(8)
            {
                crate::instrumentation::record_deterministic_work(1);
                let PointerOffsetTerm::Int32Scaled {
                    value,
                    byte_width: width,
                } = intermediate
                else {
                    continue;
                };
                if *width != byte_width {
                    continue;
                }
                let Some(Bitvector32Term::MemoryLoad(_, intermediate_address, LoadKind::Pointer)) =
                    crate::kernel::eval::viewed_as_memory_load(value)
                else {
                    continue;
                };
                if address != intermediate_address {
                    continue;
                }
                let forward = Proposition::ConditionIs(
                    ConditionTerm::pointer_offset_equal(intermediate.clone(), other_offset.clone()),
                    true,
                );
                let backward = Proposition::ConditionIs(
                    ConditionTerm::pointer_offset_equal(other_offset.clone(), intermediate.clone()),
                    true,
                );
                let premise = if self.contains_assumed_exact(&forward) {
                    forward
                } else if self.contains_assumed_exact(&backward) {
                    backward
                } else {
                    continue;
                };
                let capture =
                    crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start_active();
                let equal = crate::kernel::memory_provenance::checked_recorded_atomic_load_equality(
                    read, value, self,
                ) || crate::kernel::memory_provenance::checked_origin_load_equality(
                    read, value, self,
                );
                let mut witnesses = capture.finish();
                if !equal || witnesses.len() != 1 {
                    continue;
                }
                let equality = witnesses.pop()?;
                if !equality.checks_exact_pointer_read_terms(read, value, self) {
                    continue;
                }
                return Some(PointerOffsetCongruenceEvidence::PointerReadSnapshotAlias {
                    byte_width,
                    intermediate: Box::new(intermediate.clone()),
                    equality: Box::new(equality),
                    premise: Box::new(premise),
                    reversed,
                });
            }
        }
        None
    }

    pub(in crate::kernel) fn pointer_offset_congruence_evidence(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> Option<PointerOffsetCongruenceEvidence> {
        if left == right {
            return Some(PointerOffsetCongruenceEvidence::Exact);
        }
        let exact_premise = Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(left.clone(), right.clone()),
            true,
        );
        if self.contains_assumed_exact(&exact_premise) {
            return Some(PointerOffsetCongruenceEvidence::ExactPremise(Box::new(
                exact_premise,
            )));
        }
        let mirrored_premise = Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(right.clone(), left.clone()),
            true,
        );
        if self.contains_assumed_exact(&mirrored_premise) {
            return Some(PointerOffsetCongruenceEvidence::ExactPremise(Box::new(
                mirrored_premise,
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
        match (left, right) {
            (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
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
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) if left_width == right_width => self
                .exact_bitvector_equality_path_evidence(left, right)
                .map(|path| PointerOffsetCongruenceEvidence::Int32Scaled {
                    byte_width: *left_width,
                    path,
                })
                .or_else(|| {
                    self.direct_bitvector_equality_evidence(left, right)
                        .map(
                            |equality| PointerOffsetCongruenceEvidence::Int32ScaledDerived {
                                byte_width: *left_width,
                                equality,
                            },
                        )
                })
                .or_else(|| self.pointer_read_snapshot_scaled_evidence(left, right, *left_width)),
            (
                PointerOffsetTerm::Int64Scaled {
                    value: left,
                    byte_width: left_width,
                    unsigned: left_unsigned,
                },
                PointerOffsetTerm::Int64Scaled {
                    value: right,
                    byte_width: right_width,
                    unsigned: right_unsigned,
                },
            ) if left_width == right_width && left_unsigned == right_unsigned => {
                Some(PointerOffsetCongruenceEvidence::Int64Scaled {
                    byte_width: *left_width,
                    unsigned: *left_unsigned,
                    path: self.exact_bitvector_equality_path_evidence(left, right)?,
                })
            }
            _ => None,
        }
    }

    fn pointer_offset_element_index_evidence(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> Option<PointerOffsetCongruenceEvidence> {
        let byte_width = common_pointer_offset_element_width(left, right)?;
        let (left_index, right_index) = (
            element_index_from_offset(left, byte_width)?,
            element_index_from_offset(right, byte_width)?,
        );
        self.exact_bitvector_equality_path_evidence(&left_index, &right_index)
            .map(|path| PointerOffsetCongruenceEvidence::ElementIndex { byte_width, path })
            .or_else(|| {
                self.direct_bitvector_equality_evidence(&left_index, &right_index)
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
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<LoadAddressCongruenceEvidence> {
        let (Bitvector32Term::Variable(left), Bitvector32Term::Variable(right)) = (left, right)
        else {
            return None;
        };
        let (left_memory, left_pointer) = crate::kernel::eval::registered_load_for_variable(left)?;
        let (right_memory, right_pointer) =
            crate::kernel::eval::registered_load_for_variable(right)?;
        // Congruent addresses in one snapshot name one value only when the two
        // reads are one kind of read.
        let left_kind = crate::kernel::eval::registered_load_kind_for_variable(left)?;
        let right_kind = crate::kernel::eval::registered_load_kind_for_variable(right)?;
        if left_memory != right_memory
            || left_kind != right_kind
            || left_pointer.block != right_pointer.block
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

    pub(in crate::kernel) fn simplify_condition_under_assumptions(
        &self,
        condition: &ConditionTerm,
    ) -> ConditionTerm {
        match condition {
            ConditionTerm::AlgebraicEqual(left, right) => self
                .decide_algebraic_equality(left, right)
                .map(ConditionTerm::Constant)
                .unwrap_or_else(|| condition.clone()),
            ConditionTerm::Constant(value) => ConditionTerm::Constant(*value),
            ConditionTerm::Variable(variable) => ConditionTerm::Variable(*variable),
            ConditionTerm::Float32(CFloatCondition::Comparison {
                operator,
                left,
                right,
            }) => ConditionTerm::float32_compare(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
                *operator,
            ),
            ConditionTerm::Float32(CFloatCondition::Classification {
                classification,
                value,
            }) => ConditionTerm::float32_classification(
                self.simplify_bitvector_under_assumptions(value),
                *classification,
            ),
            ConditionTerm::Float64(CFloatCondition::Comparison {
                operator,
                left,
                right,
            }) => ConditionTerm::float64_compare(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
                *operator,
            ),
            ConditionTerm::Float64(CFloatCondition::Classification {
                classification,
                value,
            }) => ConditionTerm::float64_classification(
                self.simplify_bitvector_under_assumptions(value),
                *classification,
            ),
            ConditionTerm::PointerOffsetEqual(left, right) => {
                ConditionTerm::pointer_offset_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            ConditionTerm::PointerEqual(left, right) => {
                ConditionTerm::pointer_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            // Integer arithmetic has no memory loads; assumption-driven
            // simplification is intentionally limited to its local exact
            // constructors until the checked arithmetic planner lands.
            ConditionTerm::IntegerLessThan(left, right) => {
                ConditionTerm::integer_less_than(left.as_ref().clone(), right.as_ref().clone())
            }
            ConditionTerm::IntegerLessEqual(left, right) => {
                ConditionTerm::integer_less_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            ConditionTerm::IntegerGreaterThan(left, right) => {
                ConditionTerm::integer_greater_than(left.as_ref().clone(), right.as_ref().clone())
            }
            ConditionTerm::IntegerGreaterEqual(left, right) => {
                ConditionTerm::integer_greater_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            ConditionTerm::IntegerEqual(left, right) => {
                ConditionTerm::integer_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            ConditionTerm::IntegerNotEqual(left, right) => {
                ConditionTerm::integer_not_equal(left.as_ref().clone(), right.as_ref().clone())
            }
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
        term: &Bitvector32Term,
    ) -> Bitvector32Term {
        if let Some(value) = self.bitvector_constant_from_direct_equalities(term) {
            return Bitvector32Term::Constant(value);
        }
        match term {
            Bitvector32Term::MachineIntegerConstant(value) => {
                Bitvector32Term::MachineIntegerConstant(*value)
            }

            Bitvector32Term::Constant(value) => Bitvector32Term::Constant(*value),
            Bitvector32Term::Variable(variable) => Bitvector32Term::Variable(*variable),
            Bitvector32Term::Int64Constant(value) => Bitvector32Term::Int64Constant(*value),
            Bitvector32Term::UInt64Constant(value) => Bitvector32Term::UInt64Constant(*value),
            Bitvector32Term::UInt32From64(value) => {
                match self.wide_constant_from_equalities(value) {
                    Some(bits) => Bitvector32Term::Constant(bits as u32),
                    None => Bitvector32Term::uint32_from_64(
                        self.simplify_bitvector_under_assumptions(value),
                    ),
                }
            }
            // A narrowing conversion inside its destination range is its
            // operand's carrier (`narrowed_casts`); otherwise it stays the
            // conversion of its simplified operand.
            Bitvector32Term::MachineIntegerCast {
                value,
                source,
                destination,
            } => match self.narrowed_cast_carrier(term) {
                Some(carrier) => self.simplify_bitvector_under_assumptions(&carrier),
                None => Bitvector32Term::machine_integer_cast(
                    *source,
                    *destination,
                    self.simplify_bitvector_under_assumptions(value),
                ),
            },
            Bitvector32Term::If {
                condition,
                then_term,
                else_term,
            } => match self.decide(condition) {
                Some(true) => self.simplify_bitvector_under_assumptions(then_term),
                Some(false) => self.simplify_bitvector_under_assumptions(else_term),
                None => Bitvector32Term::if_then_else(
                    condition.as_ref().clone(),
                    self.simplify_bitvector_under_assumptions(then_term),
                    self.simplify_bitvector_under_assumptions(else_term),
                ),
            },
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => Bitvector32Term::range_fold(
                self.simplify_bitvector_under_assumptions(start),
                self.simplify_bitvector_under_assumptions(end),
                self.simplify_bitvector_under_assumptions(initial),
                *accumulator,
                *item,
                self.simplify_bitvector_under_assumptions(body),
            ),
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                Bitvector32Term::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| self.simplify_bitvector_under_assumptions(argument))
                        .collect(),
                }
            }
            Bitvector32Term::ClickFunctionApplication { .. }
            | Bitvector32Term::AlgebraicMatch { .. }
            | Bitvector32Term::IntegerToMachine { .. } => term.clone(),
            Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
                Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone(), *kind)
            }
            Bitvector32Term::PointerAddress(pointer) => {
                Bitvector32Term::PointerAddress(pointer.clone())
            }
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
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.has_condition_fact(
            ConditionTerm::signed_less_equal(left.clone(), right.clone()),
            true,
        ) && self.has_condition_fact(
            ConditionTerm::signed_less_than(left.clone(), right.clone()),
            false,
        ) || self.has_condition_fact(
            ConditionTerm::signed_less_equal(right.clone(), left.clone()),
            true,
        ) && self.has_condition_fact(
            ConditionTerm::signed_less_than(right.clone(), left.clone()),
            false,
        ) || self.has_condition_fact(
            ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
            true,
        ) && self.has_condition_fact(
            ConditionTerm::signed_greater_than(left.clone(), right.clone()),
            false,
        ) || self.has_condition_fact(
            ConditionTerm::signed_greater_equal(right.clone(), left.clone()),
            true,
        ) && self.has_condition_fact(
            ConditionTerm::signed_greater_than(right.clone(), left.clone()),
            false,
        )
    }

    pub(in crate::kernel) fn range_facts_force_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((variable, constant)) = bitvector_variable_and_constant(left, right) else {
            return false;
        };

        let mut range = IntegerRangeFacts::default();
        for (condition, value) in self.condition_facts.iter() {
            if let (ConditionTerm::Bitvector32Equal(fact_left, fact_right), false) =
                (condition, *value)
                && let Some((fact_variable, excluded)) =
                    bitvector_variable_and_constant(fact_left, fact_right)
                && fact_variable == variable
            {
                range.excluded.insert(excluded);
                continue;
            }
            let Some((fact_left, fact_right, strict)) = condition_as_order_fact(condition, *value)
            else {
                continue;
            };
            match (
                bitvector_variable(&fact_left),
                signed_bitvector_constant(&fact_right),
            ) {
                (Some(fact_variable), Some(bound)) if fact_variable == variable => {
                    let upper = if strict { bound - 1 } else { bound };
                    range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
                }
                _ => {}
            }
            match (
                signed_bitvector_constant(&fact_left),
                bitvector_variable(&fact_right),
            ) {
                (Some(bound), Some(fact_variable)) if fact_variable == variable => {
                    let lower = if strict { bound + 1 } else { bound };
                    range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
                }
                _ => {}
            }
        }

        // A bound the variable is known not to equal moves past that value:
        // `0 <= x < 4` with `x != 0`, `x != 1` and `x != 2` leaves `x == 3`.
        // Each step consumes one excluded value, so the walk is bounded by
        // the facts.
        let (Some(mut lower), Some(mut upper)) = (range.lower, range.upper) else {
            return false;
        };
        while lower < upper && range.excluded.remove(&lower) {
            lower += 1;
        }
        while lower < upper && range.excluded.remove(&upper) {
            upper -= 1;
        }
        lower == upper && lower == constant
    }

    pub(in crate::kernel) fn signed_constant_known_equal(
        &self,
        term: &Bitvector32Term,
    ) -> Option<i64> {
        if let Some(value) = signed_bitvector_constant(term) {
            return Some(value);
        }

        for (condition, value) in self.condition_facts.iter() {
            let (ConditionTerm::Bitvector32Equal(left, right), true) = (condition, value) else {
                continue;
            };
            // Only a fact with a constant on one side can name a constant for
            // `term`, and `signed_bitvector_constant` is a syntactic fold.
            // Test it before the equality search, which is the expensive
            // memory-load-bridging one: the conjunction is unchanged, so this
            // decides exactly the same facts, just without proving equalities
            // whose fact could not answer the question anyway.
            let left_constant = signed_bitvector_constant(left);
            let right_constant = signed_bitvector_constant(right);
            if let Some(value) = right_constant
                && self.bitvector_terms_proven_equal(term, left)
            {
                return Some(value);
            }
            if let Some(value) = left_constant
                && self.bitvector_terms_proven_equal(term, right)
            {
                return Some(value);
            }
        }

        None
    }

    pub(in crate::kernel) fn signed_constant_after_equality_normalization(
        &self,
        term: &Bitvector32Term,
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
        term: &Bitvector32Term,
    ) -> Option<i64> {
        match self.constant_class_resolution(term, &mut BTreeSet::new()) {
            SignedConstantResolution::Known(value) => Some(value),
            SignedConstantResolution::Unknown | SignedConstantResolution::Ambiguous => None,
        }
    }

    /// A term's constant after equality normalization, read from the
    /// constant classes (`ConstantClasses`). A settled class answers by
    /// lookup. An `Unknown` class additionally decides its conditional
    /// members under this context and compares its loads with the loads of
    /// settled classes at the same address, the equalities memory reasoning
    /// proves without a fact. A term no fact mentions folds from its
    /// operands, and a load among them is compared in the same way.
    fn constant_class_resolution(
        &self,
        term: &Bitvector32Term,
        visiting: &mut BTreeSet<u64>,
    ) -> SignedConstantResolution {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(value) = signed_bitvector_constant(term) {
            return SignedConstantResolution::Known(value);
        }
        let classes = &self.constant_classes;
        if let Some(id) = classes.class_id(term) {
            let constant = classes.constant_of_class(id);
            if constant != SignedConstantResolution::Unknown || !visiting.insert(id) {
                return constant;
            }
            let mut result = SignedConstantResolution::Unknown;
            for conditional in classes.conditional_members(id) {
                result = result.merge(self.conditional_constant_resolution(&conditional, visiting));
            }
            for (member, candidate, candidate_class) in classes.bridgeable_loads(id) {
                if self.loads_bridge(&member, &candidate) {
                    result = result.merge(classes.constant_of_class(candidate_class));
                }
            }
            visiting.remove(&id);
            return result;
        }
        let mut result = match term {
            Bitvector32Term::If { .. } => self.conditional_constant_resolution(term, visiting),
            _ => super::super::constant_classes::fold_arithmetic(term, |operand| {
                self.constant_class_resolution(operand, visiting)
            }),
        };
        if result == SignedConstantResolution::Unknown
            && let Some((key, _)) = super::super::constant_classes::load_key(term)
        {
            for (candidate, candidate_class) in classes.settled_loads_at(key) {
                crate::instrumentation::record_deterministic_work(1);
                if self.loads_bridge(term, candidate) {
                    result = result.merge(classes.constant_of_class(candidate_class));
                }
            }
        }
        result
    }

    fn conditional_constant_resolution(
        &self,
        term: &Bitvector32Term,
        visiting: &mut BTreeSet<u64>,
    ) -> SignedConstantResolution {
        let Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } = term
        else {
            return SignedConstantResolution::Unknown;
        };
        match self.decide(condition) {
            Some(condition) => self
                .constant_class_resolution(if condition { then_term } else { else_term }, visiting),
            None => SignedConstantResolution::Unknown,
        }
    }

    /// Whether two loads of one memory-blind address are proved equal: the
    /// same pointer structurally, and the snapshots proved to agree there.
    fn loads_bridge(&self, left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
        let (Some(left_view), Some(right_view)) = (
            crate::kernel::eval::viewed_as_memory_load(left),
            crate::kernel::eval::viewed_as_memory_load(right),
        ) else {
            return false;
        };
        let (
            Bitvector32Term::MemoryLoad(_, left_pointer, left_kind),
            Bitvector32Term::MemoryLoad(_, right_pointer, right_kind),
        ) = (&left_view, &right_view)
        else {
            return false;
        };
        left_kind == right_kind
            && pointers_equal_ignoring_memories(left_pointer, right_pointer)
            && self.bitvector_terms_proven_equal(left, right)
    }

    pub(in crate::kernel) fn decide_signed_comparison_from_equal_constants(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        compare: impl FnOnce(i64, i64) -> bool,
    ) -> Option<bool> {
        let left = self.signed_constant_known_equal(left)?;
        let right = self.signed_constant_known_equal(right)?;
        Some(compare(left, right))
    }
}

#[cfg(test)]
mod selected_pointer_read_offset_tests {
    use super::*;

    #[test]
    fn full_pointer_read_snapshot_direct_offset_keeps_stride_and_exact_endpoints() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer::symbolic(Variable(991_610));
        let before = CMemory::new();
        let original = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&before),
            Box::new(cell.clone()),
            LoadKind::Pointer,
        );
        let held = CValue::typed_pointer(
            Pointer::loaded(cell.block.clone(), original.clone(), 4),
            CType::Int32Pointer,
        );
        let after = before.materialize_named_cell(cell.clone(), held);
        let current = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&after),
            Box::new(cell.clone()),
            LoadKind::Pointer,
        );
        let scaled = |value| PointerOffsetTerm::scale_int32(value, 4);
        let context = PureFactContext::new();
        let left = scaled(original.clone());
        let right = scaled(current.clone());
        let evidence = context
            .pointer_offset_congruence_evidence(&left, &right)
            .expect("a checked full-pointer reread preserves its numeric offset");
        assert!(evidence.checks(&left, &right, &context));
        assert!(!evidence.checks(&left, &PointerOffsetTerm::scale_int32(current, 8), &context));
        let changed = after.store(
            cell.clone(),
            CValue::typed_pointer(Pointer::symbolic(Variable(991_611)), CType::Int32Pointer),
        );
        let changed = scaled(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&changed),
            Box::new(cell),
            LoadKind::Pointer,
        ));
        assert!(!evidence.checks(&left, &changed, &context));
        assert!(
            context
                .pointer_offset_congruence_evidence(&left, &changed)
                .is_none()
        );
    }

    #[test]
    fn full_pointer_read_snapshot_rebases_only_a_numeric_offset_premise() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer::symbolic(Variable(991_600));
        let before = CMemory::new();
        let original = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&before),
            Box::new(cell.clone()),
            LoadKind::Pointer,
        );
        let held = CValue::typed_pointer(
            Pointer::loaded(cell.block.clone(), original.clone(), 4),
            CType::Int32Pointer,
        );
        let after = before.clone().materialize_named_cell(cell.clone(), held);
        let current = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&after),
            Box::new(cell.clone()),
            LoadKind::Pointer,
        );
        let target =
            PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(991_601)), 4);
        let premise = Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(
                PointerOffsetTerm::scale_int32(current, 4),
                target.clone(),
            ),
            true,
        );
        let context = PureFactContext::new().assume_proposition(premise.clone());
        let wanted = PointerOffsetTerm::scale_int32(original.clone(), 4);
        let evidence = context
            .pointer_offset_congruence_evidence(&wanted, &target)
            .expect("same full pointer cell can transport its numeric offset spelling");
        assert!(evidence.checks(&wanted, &target, &context));
        assert!(!evidence.checks(&wanted, &target, &context.without_exact_fact(&premise)));
        let narrow = PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(&before),
                Box::new(cell.clone()),
                LoadKind::Bits32,
            ),
            4,
        );
        assert!(
            context
                .pointer_offset_congruence_evidence(&narrow, &target)
                .is_none()
        );
        let stale = before.store(
            cell.clone(),
            CValue::typed_pointer(Pointer::null(), CType::Int32Pointer),
        );
        let stale_premise = Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(
                PointerOffsetTerm::scale_int32(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory_ref(&stale),
                        Box::new(cell),
                        LoadKind::Pointer,
                    ),
                    4,
                ),
                target.clone(),
            ),
            true,
        );
        let changed = PureFactContext::new().assume_proposition(stale_premise);
        assert!(
            changed
                .pointer_offset_congruence_evidence(&wanted, &target)
                .is_none()
        );
    }
}
