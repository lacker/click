use super::*;

impl PureFactContext {
    #[cfg(test)]
    /// Whether one recorded strict order fact separates `left` from `right`
    /// directly (`left < right` or `right < left`, under either term or its
    /// canonical alias). This is an indexed lookup only — no derivation, no
    /// fuel — so an assumption-free walk such as memory-derivation naming can
    /// refute an offset equality from a recorded bound without reasoning.
    pub(in crate::kernel) fn direct_strict_order_recorded(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let separated = |endpoint: &Bitvector32Term| {
            self.signed_order_bounds
                .get(endpoint)
                .is_some_and(|bounds| {
                    bounds.iter().any(|((lower, upper, strict, _), _)| {
                        *strict
                            && ((lower == left && upper == right)
                                || (lower == right && upper == left))
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
        if let Some((term, bound, _)) = unsigned_upper_bound_below_sign_bit(condition, true)
            && let Some(value) = self.decide_unsigned_upper_bound_by_signed_order(term, bound)
        {
            return Some(value);
        }
        if let Some(value) = self.decide_from_order_rules(condition) {
            return Some(value);
        }
        // Successor rules the memory-resolution prover reads the same way
        // (`proves_order_condition_for_memory_resolution`), after the direct
        // rules have missed. Each asks one smaller strict question.
        let (lower, upper, strict) = condition_as_order_fact(condition, true)?;
        if let Some((below, above)) = successor_bound_as_strict_order(&lower, &upper, strict)
            && self.decide(&ConditionTerm::signed_less_than(below, above)) == Some(true)
        {
            return Some(true);
        }
        if let Some(((below, above, reduced_strict), base)) =
            constant_below_successor_as_order(&lower, &upper, strict)
            && self.decide(&order_condition(below, above, reduced_strict)) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(
                base,
                Bitvector32Term::Constant(i32::MAX as u32),
            )) == Some(true)
        {
            return Some(true);
        }
        self.signed_bound_from_unsigned_order(&lower, &upper, strict)
            .then_some(true)
    }

    /// Whether a signed bound between a plain variable `t` and a constant
    /// follows from an unsigned order chain on `t`, read in the biased
    /// encoding [`ConditionTerm::unsigned_less_than`] writes unsigned order
    /// in: `t <u n` is `(t ^ 2^31) <s (n ^ 2^31)`, so an unsigned chain
    /// `t <u n`, `n <=u 4` is the signed chain `t ^ 2^31 < n ^ 2^31 <=
    /// 4 ^ 2^31`, which the order walk composes as it does any signed chain.
    ///
    /// * `c <= t` for `c <= 0` (or `c < t` for `c < 0`) holds when
    ///   `t <=u INT_MAX`: the sign bit of `t` is clear, so `0 <= t`.
    /// * `t <= c` for `c >= 0` (or `t < c` for `c > 0`) holds when
    ///   `t <=u c` (or `t <u c`): `t` lies in `0..=c` (or `0..c`), where the
    ///   unsigned and signed readings agree.
    ///
    /// Only the flipped spelling `t ^ 2^31` is walked, and the walk matches
    /// endpoints by spelling, so a signed fact on `t` itself is a different
    /// endpoint: a chain mixing `t <u n` with a signed `n < 4` does not
    /// compose here. A wrapped bound (`t <u n - 1u` with `n` possibly zero)
    /// is the flipped atom `(n - 1) ^ 2^31`, which no rule relates to
    /// `n ^ 2^31`. One indexed walk from `t ^ 2^31`
    /// ([`Self::has_order_path_for_memory_resolution`]); the flipped atom of
    /// a plain variable is filed like the variable (`order_walk_atom`).
    fn signed_bound_from_unsigned_order(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        const SIGN_BIT: u32 = 0x8000_0000;
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
        if !order_walk_plain_variable(term) {
            return false;
        }
        let flipped =
            Bitvector32Term::bitwise_xor(term.clone(), Bitvector32Term::Constant(SIGN_BIT));
        // A walk needs an edge out of the flipped atom: an unsigned upper
        // bound on `t`. Asked by key first, so a signed question about a
        // variable no unsigned bound names costs one lookup, not the filing
        // of the fact set the walk reads.
        let has_unsigned_bound = self
            .signed_order_bounds
            .get(&crate::kernel::eval::canonical_term(&flipped))
            .is_some_and(|bounds| bounds.iter().any(|((_, _, _, below), _)| *below));
        has_unsigned_bound
            && self.has_order_path_for_memory_resolution(
                &flipped,
                &Bitvector32Term::Constant(target ^ SIGN_BIT),
                walk_strict,
            )
    }

    fn decide_from_order_rules(&self, condition: &ConditionTerm) -> Option<bool> {
        match condition {
            ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerEqual(left, right) => {
                if self.pointers_known_equal(left, right) {
                    Some(true)
                } else {
                    left.blocks_proven_distinct(right).then_some(false)
                }
            }
            ConditionTerm::Bitvector64Equal(left, right) => {
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
                            return self.decide(&ConditionTerm::equal(
                                index.clone(),
                                Bitvector32Term::Constant(element as u32),
                            ));
                        }
                        let left_index = int32_element_index_from_offset(left);
                        let right_index = int32_element_index_from_offset(right);
                        match (left_index, right_index) {
                            (Some(left_index), Some(right_index)) => exact_or_unequal(
                                self.decide(&ConditionTerm::equal(left_index, right_index)),
                                self.rebuilt_offset_is_exact(left, 4, false)
                                    && self.rebuilt_offset_is_exact(right, 4, false),
                            ),
                            _ => {
                                let left_bytes = byte_offset_from_pointer_offset(left);
                                let right_bytes = byte_offset_from_pointer_offset(right);
                                match (left_bytes, right_bytes) {
                                    (Some(left_bytes), Some(right_bytes)) => exact_or_unequal(
                                        self.decide(&ConditionTerm::equal(left_bytes, right_bytes)),
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
            ConditionTerm::Bitvector32Equal(left, right) if left == right => Some(true),
            ConditionTerm::Bitvector32Equal(left, right) => {
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
                    return self.decide(&ConditionTerm::equal(left, right));
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
            ConditionTerm::Bitvector32SignedLessThan(left, right) if left == right => Some(false),
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) if left == right => {
                Some(false)
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right) if left == right => Some(true),
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) if left == right => {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if let Some(result) = self.decide_signed_comparison_from_equal_constants(
                    &left,
                    &right,
                    |left, right| left < right,
                ) {
                    return Some(result);
                }
                if right == signed_int_min_term() || left == signed_int_max_term() {
                    return Some(false);
                }
                if self.subtract_same_const_order_fact(&left, &right, true)
                    || self.has_order_path(&left, &right, true)
                    || (self.has_condition_fact(
                        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                        true,
                    ) && self.has_condition_fact(
                        ConditionTerm::equal(left.clone(), right.clone()),
                        false,
                    ))
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_upper_bound_below(&left, &right)
                    || self.has_successor_upper_bound_below(&left, &right)
                    || self.has_add_const_upper_bound_below(&left, &right)
                    || self.has_lower_bound_above(&right, &left)
                    || self.has_add_const_lower_bound_above(&right, &left)
                    || self.positive_offset_is_proven_above(&left, &right)
                    || self.positive_subtraction_is_proven_below(&left, &right)
                    // Consulted last: every earlier rule keeps its cost.
                    || self.has_subtract_const_upper_bound(&left, &right, true)
                    || self.has_subtract_const_lower_bound(&right, &left, true)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                ) || self.has_condition_fact(
                    ConditionTerm::signed_less_equal(right.clone(), left.clone()),
                    true,
                ) || self.has_order_path(&right, &left, true)
                    || self.order_facts_force_equal(&left, &right)
                {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval(&left, &right, true)
                }
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if let Some(result) = self.decide_signed_comparison_from_equal_constants(
                    &left,
                    &right,
                    |left, right| left <= right,
                ) {
                    return Some(result);
                }
                if order_holds_at_int32_extreme(&left, &right, false) {
                    return Some(true);
                }
                if let Some(base) = left.add_const_base(1)
                    && self.condition_facts.iter().any(|(condition, value)| {
                        let (ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right), true) =
                            (condition, value)
                        else {
                            return false;
                        };
                        fact_left.as_ref() == &base
                            && bitvector_terms_proven_equal_for_memory_resolution(
                                fact_right,
                                &right,
                                self,
                            )
                    })
                {
                    return Some(true);
                }
                if self.has_order_path(&left, &right, false)
                    || left.add_const_base(1).is_some_and(|base| {
                        self.has_condition_fact(
                            ConditionTerm::signed_less_than(base, right.clone()),
                            true,
                        )
                    })
                    || right.subtract_one_base().is_some_and(|base| {
                        let zero = Bitvector32Term::Constant(0);
                        left == zero
                            && (self.has_condition_fact(
                                ConditionTerm::signed_greater_than(base.clone(), zero.clone()),
                                true,
                            ) || self.has_lower_bound_above(&base, &zero))
                    })
                    || self.has_add_const_upper_bound_at_or_below(&left, &right)
                    || self.is_bounded_by_base_before_nonnegative_offset(&left, &right)
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_at_or_above(&right, &left)
                    || self.has_add_const_lower_bound_at_or_above(&right, &left)
                    || self.nonnegative_offset_is_proven_at_or_above(&left, &right)
                    || self.order_facts_force_equal(&left, &right)
                    // Consulted last: every earlier rule keeps its cost.
                    || self.has_subtract_const_upper_bound(&left, &right, false)
                    || self.has_subtract_const_lower_bound(&right, &left, false)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                    true,
                ) {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval(&left, &right, false)
                }
            }
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if let Some(result) = self.decide_signed_comparison_from_equal_constants(
                    &left,
                    &right,
                    |left, right| left > right,
                ) {
                    return Some(result);
                }
                if right == signed_int_max_term() || left == signed_int_min_term() {
                    return Some(false);
                }
                if self.has_order_path(&right, &left, true)
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_above(&left, &right)
                    || self.has_add_const_lower_bound_above(&left, &right)
                    // The mirrors of the `<` rules for a successor and for
                    // the int32 maximum, so `x + 1 > x` and `INT32_MAX > x`
                    // are decided as `x < x + 1` and `x < INT32_MAX` are.
                    || self.positive_offset_is_proven_above(&right, &left)
                    || left == signed_int_max_term()
                        && self.decide(&ConditionTerm::signed_less_than(
                            right.clone(),
                            left.clone(),
                        )) == Some(true)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                ) || self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(right.clone(), left.clone()),
                    true,
                ) || self.order_facts_force_equal(&left, &right)
                {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval(&right, &left, true)
                }
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if let Some(result) = self.decide_signed_comparison_from_equal_constants(
                    &left,
                    &right,
                    |left, right| left >= right,
                ) {
                    return Some(result);
                }
                if order_holds_at_int32_extreme(&right, &left, false) {
                    return Some(true);
                }
                if self.has_order_path(&right, &left, false)
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_at_or_above(&left, &right)
                    || self.has_add_const_lower_bound_at_or_above(&left, &right)
                    // The mirror of the `<=` successor rule, so `x + 1 >= x`
                    // is decided as `x <= x + 1` is.
                    || self.nonnegative_offset_is_proven_at_or_above(&right, &left)
                    || self.order_facts_force_equal(&left, &right)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_less_than(left.clone(), right.clone()),
                    true,
                ) {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval(&right, &left, false)
                }
            }
            _ => None,
        }
    }

    /// Query equality already known to the trusted graph. This performs no
    /// arithmetic proof search, alias-component walk, or resource check.
    /// `false` means unknown, not unequal. Memory consumers must retain their
    /// structural-distinctness and separation checks around this query.
    pub(in crate::kernel) fn pointers_known_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        self.equality_graph.are_equal(left, right)
    }

    /// True when some exact order fact strictly bounds `term` above
    /// (`term < y` for any `y`). A strict signed bound pins
    /// `term < INT_MAX`, which is what discharges `term + 1` overflow
    /// is checked from exact facts alone.
    pub(in crate::kernel) fn has_exact_strict_upper_bound(&self, term: &Bitvector32Term) -> bool {
        self.condition_order_facts()
            .iter()
            .any(|(edge_left, _, strict)| *strict && edge_left == term)
    }

    pub(in crate::kernel) fn has_order_path(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let order_facts = self.condition_order_facts();
        self.has_order_path_in_facts(left, right, require_strict, &order_facts)
    }

    /// Retain the exact signed-order edges selected by a deterministic path
    /// decision. This deliberately accepts only syntactic edge joins (plus a
    /// context-free constant tail): equality, memory-DAG, quantified, and
    /// derived-edge joins need their own typed evidence before they may be
    /// exported as certificate provenance.
    pub(in crate::kernel) fn exact_signed_order_path_evidence(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> Option<Vec<SignedOrderDerivationStep>> {
        // Keep the exact source proposition alongside the normalized edge.
        // `condition_as_order_fact` intentionally normalizes polarity (for
        // example, false `x <= y` becomes `y < x`); check must check the
        // proposition that was actually present, not merely the normalized
        // form. This collection is local to derivation construction so
        // the durable evidence remains self-contained.
        let order_facts = self
            .condition_facts
            .iter()
            .filter_map(|(condition, value)| {
                condition_as_order_fact(condition, *value).map(|(lower, upper, strict)| {
                    SignedOrderDerivationStep {
                        lower,
                        upper,
                        strict,
                        premise: Proposition::ConditionIs(condition.clone(), *value),
                    }
                })
            })
            .collect::<Vec<_>>();
        let terms_match = |current: &Bitvector32Term, other: &Bitvector32Term| {
            current == other
                || crate::kernel::api::extended_dag_bridging_active()
                    && crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                        current, other, self,
                    )
        };
        let mut stack = vec![(left.clone(), false, Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far, path)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (terms_match(&current, right) || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
                && !path.is_empty()
            {
                return Some(path);
            }
            for edge in order_facts.iter().rev() {
                let constant_connection = signed_bitvector_constant(&current)
                    .zip(signed_bitvector_constant(&edge.lower))
                    .and_then(|(current, edge_left)| {
                        (current <= edge_left).then_some(current < edge_left)
                    });
                if !terms_match(&current, &edge.lower) && constant_connection.is_none() {
                    continue;
                }
                let mut extended = path.clone();
                extended.push(edge.clone());
                stack.push((
                    edge.upper.clone(),
                    strict_so_far || edge.strict || constant_connection == Some(true),
                    extended,
                ));
            }
        }
        None
    }

    /// The exact 64-bit order facts that chain `left` up to `right`, of one
    /// kind: unsigned `uint64` facts when `unsigned`, signed `int64` ones
    /// otherwise. Each step keeps the proposition the context holds, as
    /// [`Self::exact_signed_order_path_evidence`] does for `int32`. The chain
    /// meets `right` at the same canonical term; a constant connection is
    /// left to other rules, since `simp` writes no lemma for it.
    pub(in crate::kernel) fn exact_wide_order_path_evidence(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
        unsigned: bool,
    ) -> Option<Vec<SignedOrderDerivationStep>> {
        let canonical = crate::kernel::eval::canonical_term;
        let order_facts = self
            .condition_facts
            .iter()
            .filter_map(|(condition, value)| {
                crate::instrumentation::record_deterministic_work(1);
                wide_order_fact(condition, *value, unsigned).map(|(lower, upper, strict)| {
                    SignedOrderDerivationStep {
                        lower,
                        upper,
                        strict,
                        premise: Proposition::ConditionIs(condition.clone(), *value),
                    }
                })
            })
            .collect::<Vec<_>>();
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
            for edge in order_facts.iter().rev() {
                crate::instrumentation::record_deterministic_work(1);
                if canonical(&edge.lower) != current {
                    continue;
                }
                let mut extended = path.clone();
                extended.push(edge.clone());
                stack.push((
                    canonical(&edge.upper),
                    strict_so_far || edge.strict,
                    extended,
                ));
            }
        }
        None
    }

    pub(in crate::kernel) fn has_exact_order_path(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let order_facts = self.condition_order_facts();
        // Two forms of one load at different snapshots connect along
        // recorded memory-derivation edges; the walk is deterministic (exact
        // facts plus DAG edges, no ambient condition reasoning), so an exact
        // order path may link through it — inside the loadable prover's
        // extended-bridging scope only. Non-loads still match verbatim.
        let terms_match = |current: &Bitvector32Term, other: &Bitvector32Term| {
            current == other
                || crate::kernel::api::extended_dag_bridging_active()
                    && crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                        current, other, self,
                    )
        };
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (terms_match(&current, right) || constant_connection.is_some())
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
                if terms_match(&current, edge_left) || constant_connection.is_some() {
                    stack.push((
                        edge_right.clone(),
                        strict_so_far || *edge_strict || constant_connection == Some(true),
                    ));
                }
            }
        }
        false
    }

    pub(in crate::kernel) fn has_order_path_in_facts(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
        order_facts: &[(Bitvector32Term, Bitvector32Term, bool)],
    ) -> bool {
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (self.bitvector_terms_equal_for_transport(&current, right)
                || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
            {
                return true;
            }
            for (edge_left, edge_right, edge_strict) in order_facts {
                if self.bitvector_terms_equal_for_transport(&current, edge_left) {
                    stack.push((edge_right.clone(), strict_so_far || *edge_strict));
                }
            }
        }
        false
    }

    /// The filing of this fact set that
    /// [`Self::has_order_path_for_memory_resolution`] walks, shared by
    /// fact-set identity exactly as [`Self::condition_order_facts`] is.
    fn order_walk_index(&self) -> std::rc::Rc<OrderWalkIndex> {
        let memo_id = super::super::dag_memo_assumptions_id(self);
        if let Some(hit) = ORDER_WALK_INDEX_MEMO.with(|memo| memo.borrow().get(&memo_id).cloned()) {
            crate::kernel::assumptions::reasoning_interrupted();
            return hit;
        }
        let facts = self.condition_order_facts();
        let mut complete = true;
        let mut by_lower = BTreeMap::<Bitvector32Term, Vec<usize>>::new();
        let mut by_exact_constant = BTreeMap::<i64, Vec<usize>>::new();
        let mut by_written_constant = BTreeMap::<i64, Vec<usize>>::new();
        let mut open = Vec::new();
        for (index, (lower, _, _)) in facts.iter().enumerate() {
            if !order_walk_keyable(lower) {
                open.push(index);
                continue;
            }
            // Filed under its canonical form too: the recorded-equality class
            // a node looks up is spelled canonically.
            let canonical = crate::kernel::eval::canonical_term(lower);
            if &canonical != lower {
                by_lower.entry(canonical).or_default().push(index);
            }
            by_lower.entry(lower.clone()).or_default().push(index);
            if let Some(constant) = crate::kernel::assumptions::exact_signed_constant(lower, self) {
                by_exact_constant.entry(constant).or_default().push(index);
            }
            if let Some(constant) = signed_bitvector_constant(lower) {
                by_written_constant.entry(constant).or_default().push(index);
            }
        }
        let mut equalities = Vec::new();
        let mut equalities_by_side = BTreeMap::<Bitvector32Term, Vec<usize>>::new();
        let mut offset_equality_atoms = BTreeSet::new();
        for (condition, value) in self.condition_facts.iter() {
            if crate::kernel::assumptions::reasoning_interrupted() {
                complete = false;
                break;
            }
            if !*value {
                continue;
            }
            match condition {
                ConditionTerm::Bitvector32Equal(left, right) => {
                    let index = equalities.len();
                    equalities.push((left.as_ref().clone(), right.as_ref().clone()));
                    for side in [left.as_ref(), right.as_ref()] {
                        if order_walk_keyable(side) {
                            let filed = equalities_by_side.entry(side.clone()).or_default();
                            if filed.last() != Some(&index) {
                                filed.push(index);
                            }
                        }
                    }
                }
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    for side in [left.as_ref(), right.as_ref()] {
                        if let PointerOffsetTerm::Int32Scaled { value, .. } = side {
                            offset_equality_atoms.insert(value.as_ref().clone());
                        }
                    }
                }
                _ => {}
            }
        }
        let offset_equality_lowers = facts
            .iter()
            .enumerate()
            .filter(|(_, (lower, _, _))| {
                order_walk_keyable(lower) && offset_equality_atoms.contains(lower)
            })
            .map(|(index, _)| index)
            .collect();
        let open_memory_free = open
            .iter()
            .all(|edge| order_reach_memory_free(&facts[*edge].0));
        let index = std::rc::Rc::new(OrderWalkIndex {
            open_memory_free,
            facts,
            by_lower,
            by_exact_constant,
            by_written_constant,
            offset_equality_lowers,
            open,
            equalities,
            equalities_by_side,
            offset_equality_atoms,
        });
        // As for the order-fact collection: only a complete filing is shared.
        if complete {
            ORDER_WALK_INDEX_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= ORDER_WALK_INDEX_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(memo_id, index.clone());
            });
        }
        index
    }

    /// The edges of `index` the order walk's node `current` can match,
    /// ascending, or `None` when the node must read every edge.
    ///
    /// The walk's edge test is
    /// `bitvector_terms_proven_equal_for_memory_resolution(current, lower)`
    /// or, for two written constants, `current <= lower`. When `current` and
    /// `lower` are each a constant or an [`order_walk_atom`] (a variable that
    /// cannot name a load, or its sign-bit flip), that comparison has exactly
    /// these routes: structural identity, two
    /// exact constants (which then decide it outright, true or false), the
    /// trusted graph (`int32_values_known_equal`), and an exact
    /// offset-equality fact over the two scaled terms. Every other route
    /// needs a load (the load view of a load variable, the value stored under
    /// a load, two loads' derivations) or a sum (additive cancellation, a
    /// zero addend, congruence), and neither side of such a pair is one. So
    /// a keyable node reads:
    ///
    /// * the open edges, whose lower endpoint is anything else;
    /// * when it has an exact constant, the edges whose lower endpoint has
    ///   the same one; one with a different constant is refused outright;
    /// * the edges filed under a member of its recorded-equality class, which
    ///   is everything the equality graph reaches;
    /// * when it is a written constant, the edges whose written constant
    ///   lower endpoint is at least it, and the edges whose lower endpoint an
    ///   offset equality scales — a scaled constant is a constant offset,
    ///   which such a fact can equate with a scaled variable.
    ///
    /// An atom an offset equality scales itself is declined: that route
    /// could reach any endpoint the fact names.
    fn order_walk_filed_edges(
        &self,
        index: &OrderWalkIndex,
        current: &Bitvector32Term,
    ) -> Option<Vec<usize>> {
        let written = signed_bitvector_constant(current);
        if written.is_none()
            && (!order_walk_atom(current) || index.offset_equality_atoms.contains(current))
        {
            return None;
        }
        let mut edges = index.open.clone();
        if let Some(constant) = crate::kernel::assumptions::exact_signed_constant(current, self)
            && let Some(filed) = index.by_exact_constant.get(&constant)
        {
            edges.extend_from_slice(filed);
        }
        let canonical = crate::kernel::eval::canonical_term(current);
        let keys = std::iter::once(current.clone())
            .chain((&canonical != current).then_some(canonical))
            .chain(self.bitvector_equality_class(current));
        for key in keys {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(filed) = index.by_lower.get(&key) {
                edges.extend_from_slice(filed);
            }
        }
        if let Some(constant) = written {
            for (_, filed) in index.by_written_constant.range(constant..) {
                crate::instrumentation::record_deterministic_work(1);
                edges.extend_from_slice(filed);
            }
            edges.extend_from_slice(&index.offset_equality_lowers);
        }
        edges.sort_unstable();
        edges.dedup();
        Some(edges)
    }

    pub(in crate::kernel) fn has_order_path_for_memory_resolution(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        let walk_index = self.order_walk_index();
        let order_facts = walk_index.facts.clone();
        let order_terms_match = |left: &Bitvector32Term, right: &Bitvector32Term| {
            if left == right {
                return true;
            }
            let (
                Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
                Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
            ) = (left, right)
            else {
                return false;
            };
            // The question is about *this* load, so it is asked about this
            // load's pointer. `memory_snapshots_proven_equal_at_pointer` is
            // the one comparison that answers it: it tries structural
            // agreement, the canonical projection for this pointer, the
            // bounded per-load bridge — which is what carries the cell across
            // a call's havoc block where a whole-memory equality would fail —
            // and finally every cell the two snapshots differ on, kept or
            // dropped by `observable_by_load` and then proven distinct from
            // this pointer.
            //
            // This used to try the pointerless whole-snapshot equality first,
            // and that equality drops every `local:` cell before comparing.
            // For a load through a pointer the verifier cannot resolve, that
            // is the withdrawn `Symbolic` exception spelled on the other side:
            // it claims no automatic object is memory such a load reads, which
            // `q = echo(&x)` refutes. Two snapshots differing only in
            // `local:x` were therefore the same term here, so an order fact
            // about `q[0]` outlived `x = 1`.
            left_pointer == right_pointer
                && left_kind == right_kind
                && memory_snapshots_proven_equal_at_pointer(
                    left_memory,
                    right_memory,
                    left_pointer,
                    self,
                )
        };
        // Every int32 value is at most `INT32_MAX`, so a walk toward it is
        // done as soon as it has the strictness it needs: `x < y` alone gives
        // `x < INT32_MAX`, as the condition checker also concludes.
        let right_is_int32_max = right == &Bitvector32Term::Constant(i32::MAX as u32);
        // What earlier walks toward this target learned about the states they
        // expanded (`OrderReachMemo`). Any walk reads it; only a walk that
        // expanded no state reading memory adds to it.
        let reach_key = self.order_reach_key(&walk_index, right, require_strict);
        let mut memory_free_walk = reach_key.is_some();
        let mut parents = BTreeMap::<OrderReachState, OrderReachState>::new();
        let epoch_before = crate::kernel::assumptions::incomplete_reasoning_epoch();
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if crate::kernel::assumptions::reasoning_interrupted() {
                return false;
            }
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            memory_free_walk &= order_reach_memory_free(&current);
            if let Some(key) = &reach_key {
                match order_reach_lookup(key, &current, strict_so_far) {
                    Some(true) => {
                        if memory_free_walk {
                            record_order_reach_path(key, &parents, (current, strict_so_far));
                        }
                        return true;
                    }
                    // Nothing this state reaches passes the target test, so
                    // neither does anything the walk would find through it.
                    Some(false) => continue,
                    None => {}
                }
            }
            if right_is_int32_max && (!require_strict || strict_so_far) {
                if let Some(key) = reach_key.as_ref().filter(|_| memory_free_walk) {
                    record_order_reach_path(key, &parents, (current, strict_so_far));
                }
                return true;
            }
            let target_constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            let target_positive_offset =
                self.positive_offset_is_proven_above_for_memory_resolution(&current, right);
            if (bitvector_terms_proven_equal_for_memory_resolution(&current, right, self)
                || target_positive_offset
                || target_constant_connection.is_some())
                && (!require_strict
                    || strict_so_far
                    || target_positive_offset
                    || target_constant_connection == Some(true))
            {
                if let Some(key) = reach_key.as_ref().filter(|_| memory_free_walk) {
                    record_order_reach_path(key, &parents, (current, strict_so_far));
                }
                return true;
            }
            // Each state this one pushes first is reached through it, for the
            // path a success records.
            let mut push = |stack: &mut Vec<OrderReachState>, next: OrderReachState| {
                if reach_key.is_some() && !seen.contains(&next) && !parents.contains_key(&next) {
                    parents.insert(next.clone(), (current.clone(), strict_so_far));
                }
                stack.push(next);
            };
            // The edges and equalities this node can match, in fact order.
            // A node the filing covers reads its own entries; any other node
            // reads every fact, as the walk always did.
            let full_scan = order_walk_full_scan_forced();
            let filed = (!full_scan)
                .then(|| self.order_walk_filed_edges(&walk_index, &current))
                .flatten();
            let equalities_filed = !full_scan && order_walk_keyable(&current);
            let edges = filed.unwrap_or_else(|| (0..order_facts.len()).collect());
            for edge in edges {
                let (edge_left, edge_right, edge_strict) = &order_facts[edge];
                if crate::kernel::assumptions::reasoning_interrupted() {
                    return false;
                }
                let constant_connection = signed_bitvector_constant(&current)
                    .zip(signed_bitvector_constant(edge_left))
                    .and_then(|(current, edge_left)| {
                        (current <= edge_left).then_some(current < edge_left)
                    });
                if bitvector_terms_proven_equal_for_memory_resolution(&current, edge_left, self)
                    || constant_connection.is_some()
                {
                    push(
                        &mut stack,
                        (
                            edge_right.clone(),
                            strict_so_far || *edge_strict || constant_connection == Some(true),
                        ),
                    );
                }
            }
            // `order_terms_match` is structural identity unless both sides
            // are loads, so a node that is not a load matches exactly the
            // equalities that spell it as a side.
            let equalities = if equalities_filed {
                walk_index
                    .equalities_by_side
                    .get(&current)
                    .cloned()
                    .unwrap_or_default()
            } else {
                (0..walk_index.equalities.len()).collect()
            };
            for equality in equalities {
                let (left, right) = &walk_index.equalities[equality];
                if crate::kernel::assumptions::reasoning_interrupted() {
                    return false;
                }
                if order_terms_match(&current, left) {
                    push(&mut stack, (right.clone(), strict_so_far));
                }
                if order_terms_match(&current, right) {
                    push(&mut stack, (left.clone(), strict_so_far));
                }
            }
        }
        // A complete refusal: every state the walk reached was expanded, and
        // none reaches a state that passes the target test.
        if let Some(key) = reach_key.as_ref().filter(|_| memory_free_walk)
            && crate::kernel::assumptions::incomplete_reasoning_epoch() == epoch_before
            && !crate::kernel::assumptions::reasoning_interrupted()
        {
            record_order_reach_refusal(key, seen);
        }
        false
    }

    /// The memo key for walks toward `right`, or `None` where the walk may
    /// not share what it learns: a walk run as the full-scan reference, a
    /// target that reads memory, or a fact set with an order edge whose
    /// lower endpoint reads memory.
    ///
    /// Between terms that read no memory — integer arithmetic over constants
    /// and variables that name no load — every test the walk applies (the
    /// edge test, the equality match, the target test) is a question about
    /// the fact set alone: no load view, no snapshot comparison, no memory
    /// DAG. Every node a walk reaches is either the target, the source, an
    /// edge's upper endpoint or an equality's side, and a walk that reaches
    /// one that reads memory stops recording (`order_reach_memory_free`).
    fn order_reach_key(
        &self,
        index: &OrderWalkIndex,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> Option<OrderReachKey> {
        (!order_walk_full_scan_forced() && index.open_memory_free && order_reach_memory_free(right))
            .then(|| OrderReachKey {
                facts: super::super::dag_memo_assumptions_id(self),
                target: right.clone(),
                require_strict,
            })
    }

    fn positive_offset_is_proven_above_for_memory_resolution(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        let Some((term_base, addend)) = term.add_const_parts() else {
            return false;
        };
        if addend != 1
            || !bitvector_terms_proven_equal_for_memory_resolution(&term_base, base, self)
        {
            return false;
        }
        self.condition_facts.iter().any(|(condition, value)| {
            matches!(
                (condition, value),
                (ConditionTerm::Bitvector32SignedLessThan(left, _), true)
                    if bitvector_terms_proven_equal_for_memory_resolution(left, base, self)
            ) || matches!(
                (condition, value),
                (ConditionTerm::Bitvector32SignedGreaterThan(_, right), true)
                    if bitvector_terms_proven_equal_for_memory_resolution(right, base, self)
            )
        })
    }

    pub(in crate::kernel) fn proves_order_condition_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        // The biased spelling of an unsigned bound below the sign bit is the
        // signed pair `0 <= term` and `term <= bound`, read the same way the
        // condition checker reads it (`unsigned_upper_bound_below_sign_bit`),
        // so the two provers agree on what a range's extent guard means.
        if value
            && let Some((term, bound, _)) = unsigned_upper_bound_below_sign_bit(condition, true)
        {
            return self.proves_order_condition_for_memory_resolution(
                &ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), term.clone()),
                true,
            ) && self.proves_order_condition_for_memory_resolution(
                &ConditionTerm::signed_less_equal(term.clone(), Bitvector32Term::Constant(bound)),
                true,
            );
        }
        condition_as_order_fact(condition, value).is_some_and(|(left, right, strict)| {
            // The extreme and successor rules are the ones the condition
            // checker reads the same way (`decide_from_order_facts`); the
            // successor rules run only after the path search has missed.
            if order_holds_at_int32_extreme(&left, &right, strict) {
                return true;
            }
            let simplified_left = self.simplify_bitvector_under_assumptions(&left);
            let simplified_right = self.simplify_bitvector_under_assumptions(&right);
            if self.has_order_path_for_memory_resolution(
                &simplified_left,
                &simplified_right,
                strict,
            ) {
                return true;
            }
            if let Some((below, above)) = successor_bound_as_strict_order(&left, &right, strict)
                && self.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_than(below, above),
                    true,
                )
            {
                return true;
            }
            constant_below_successor_as_order(&left, &right, strict).is_some_and(
                |((below, above, reduced_strict), base)| {
                    self.proves_order_condition_for_memory_resolution(
                        &order_condition(below, above, reduced_strict),
                        true,
                    ) && self.proves_order_condition_for_memory_resolution(
                        &ConditionTerm::signed_less_than(
                            base,
                            Bitvector32Term::Constant(i32::MAX as u32),
                        ),
                        true,
                    )
                },
            )
        })
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
    let mut index = 0;
    while index < left_addends.len() {
        if let Some(shared) = right_addends
            .iter()
            .position(|addend| addend == &left_addends[index])
        {
            left_addends.remove(index);
            right_addends.remove(shared);
        } else {
            index += 1;
        }
    }
    (rebuild(left_addends), rebuild(right_addends))
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
                    let fact = ConditionTerm::pointer_aligned(base_pointer.clone(), probe);
                    if self.exact_condition_value(&fact) == Some(true) {
                        found = Some(Proposition::ConditionIs(fact, true));
                        break 'candidates;
                    }
                    let witness = allow_class_witness
                        .then(|| self.equality_graph.alignment_witness(&base_pointer))
                        .flatten()
                        .filter(|(known, _)| probe <= *known)
                        .map(|(known, source)| ConditionTerm::pointer_aligned(source, known));
                    let fact = witness.unwrap_or(fact);
                    if self.exact_condition_value(&fact) == Some(true) {
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
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        let mut used = crate::kernel::eval::pointer_tags::UsedFacts::new();
        self.decide_uint64_equality_extras_citing(left, right, &mut used)
    }

    /// The complete pointer-word decision for a 64-bit equality, citing the
    /// exact facts used: the address rule, the alignment rule, and the tag
    /// extras, in that order.
    pub(in crate::kernel) fn decide_pointer_word_equality_citing(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        if let Some(pointer_condition) =
            ConditionTerm::address_equality_as_pointer_equality(left, right)
        {
            return self.decide_citing(&pointer_condition, used);
        }
        let condition =
            ConditionTerm::Bitvector64Equal(Box::new(left.clone()), Box::new(right.clone()));
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
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        use crate::kernel::eval::pointer_tags::{masked_tag_value, tag_bound, tagged_address_form};
        let left_form = tagged_address_form(left, self, used);
        let right_form = tagged_address_form(right, self, used);
        match (left_form, right_form) {
            (Some(left), Some(right)) => {
                if left.tag == right.tag {
                    return self.decide_citing(
                        &ConditionTerm::pointer_equal(left.pointer, right.pointer),
                        used,
                    );
                }
                if left.pointer == right.pointer {
                    return self
                        .decide_citing(&ConditionTerm::uint64_equal(left.tag, right.tag), used);
                }
                let (Some(left_tag), Some(right_tag)) =
                    (tag_bound(&left.tag), tag_bound(&right.tag))
                else {
                    return None;
                };
                let alignment = left_tag
                    .max(right_tag)
                    .checked_add(1)?
                    .checked_next_power_of_two()?;
                let distinct = self.decide_citing(
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
                // Distinct aligned bases differ by at least `alignment`, so
                // tags below it cannot make the words coincide.
                (distinct && both_aligned).then_some(false)
            }
            (Some(form), None) | (None, Some(form)) => {
                let left_is_form =
                    tagged_address_form(left, self, &mut Default::default()).is_some();
                let other = if left_is_form { right } else { left };
                if other.uint64_as_const() != Some(0) {
                    return None;
                }
                let tag = tag_bound(&form.tag)?;
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
                    return self
                        .decide_citing(&ConditionTerm::uint64_equal(tag, right.clone()), used);
                }
                if let Some(tag) = masked_tag_value(right, self, used) {
                    return self
                        .decide_citing(&ConditionTerm::uint64_equal(left.clone(), tag), used);
                }
                self.decide_masked_zero(left, right, used)
            }
        }
    }

    /// `(x & m) == 0` holds when `x` is below the lowest set bit of `m`.
    fn decide_masked_zero(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        let masked = if right.uint64_as_const() == Some(0) {
            left
        } else if left.uint64_as_const() == Some(0) {
            right
        } else {
            return None;
        };
        let Bitvector32Term::UInt64BitwiseAnd(first, second) = masked else {
            return None;
        };
        let (value, mask) = match (first.uint64_as_const(), second.uint64_as_const()) {
            (None, Some(mask)) => (first, mask),
            (Some(mask), None) => (second, mask),
            _ => return None,
        };
        if mask == 0 {
            return Some(true);
        }
        let bound = 1u64.checked_shl(mask.trailing_zeros())?;
        (self.decide_citing(
            &ConditionTerm::uint64_less_than(
                value.as_ref().clone(),
                Bitvector32Term::UInt64Constant(bound),
            ),
            used,
        ) == Some(true))
        .then_some(true)
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
    fn constant_factor(term: &Bitvector32Term) -> Option<i64> {
        match term {
            Bitvector32Term::Multiply(left, right) => left
                .as_const()
                .map(|constant| i64::from(constant as i32))
                .or_else(|| right.as_const().map(|constant| i64::from(constant as i32))),
            _ => None,
        }
    }
    let divisible = |part: &PointerOffsetTerm| match part {
        PointerOffsetTerm::Int32Scaled { value, byte_width }
        | PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } => {
            let scale = constant_factor(value)
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

/// The operand, inclusive bound, and source strictness of an unsigned upper
/// bound `x <=u c` (or `x <u c + 1`) whose bound `c` lies below the sign bit,
/// read back from the
/// biased encoding [`ConditionTerm::unsigned_less_equal`] builds:
/// `(x ^ 2^31) <=s (c ^ 2^31)`, held with `value`: the mirrored
/// `(c ^ 2^31) >s (x ^ 2^31)` and the refuted converses (a false
/// `(x ^ 2^31) >s c'`) read the same way [`condition_as_order_fact`] reads
/// them.
///
/// Such a bound means exactly `0 <= x` and `x <= c` in signed arithmetic: a
/// word no larger than `c < 2^31` as unsigned has a clear sign bit, and for a
/// clear sign bit the two readings agree. That is the form order facts are
/// written in, so the condition checker decides it by deciding those two, and
/// a context that assumes it files those two beside it
/// (`PureFactContext::assume_condition`), so every reader of signed order
/// facts sees the range an unsigned test established. The recognizer is a
/// constant-size match on the condition's own shape.
pub(in crate::kernel) fn unsigned_upper_bound_below_sign_bit(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(&Bitvector32Term, u32, bool)> {
    const SIGN_BIT: u32 = 0x8000_0000;
    // `(lower, upper, strict)`: the held fact is `lower < upper` when
    // strict and `lower <= upper` otherwise.
    let (left, right, strict) = match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessEqual(a, b), true)
        | (ConditionTerm::Bitvector32SignedGreaterThan(a, b), false) => (a, b, false),
        (ConditionTerm::Bitvector32SignedLessThan(a, b), true)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(a, b), false) => (a, b, true),
        (ConditionTerm::Bitvector32SignedGreaterEqual(a, b), true)
        | (ConditionTerm::Bitvector32SignedLessThan(a, b), false) => (b, a, false),
        (ConditionTerm::Bitvector32SignedGreaterThan(a, b), true)
        | (ConditionTerm::Bitvector32SignedLessEqual(a, b), false) => (b, a, true),
        _ => return None,
    };
    let term = match left.as_ref() {
        Bitvector32Term::BitwiseXor(a, b) => match (a.as_ref(), b.as_ref()) {
            (Bitvector32Term::Constant(SIGN_BIT), term)
            | (term, Bitvector32Term::Constant(SIGN_BIT)) => term,
            _ => return None,
        },
        _ => return None,
    };
    let biased = right.as_const()?;
    let bound = biased ^ SIGN_BIT;
    let bound = if strict { bound.checked_sub(1)? } else { bound };
    (bound <= i32::MAX as u32).then_some((term, bound, strict))
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
) -> Option<(&Bitvector32Term, u32, bool)> {
    let (left, right, strict) = match (condition, value) {
        (ConditionTerm::Bitvector64UnsignedLessEqual(a, b), true)
        | (ConditionTerm::Bitvector64UnsignedGreaterThan(a, b), false) => (a, b, false),
        (ConditionTerm::Bitvector64UnsignedLessThan(a, b), true)
        | (ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b), false) => (a, b, true),
        (ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b), true)
        | (ConditionTerm::Bitvector64UnsignedLessThan(a, b), false) => (b, a, false),
        (ConditionTerm::Bitvector64UnsignedGreaterThan(a, b), true)
        | (ConditionTerm::Bitvector64UnsignedLessEqual(a, b), false) => (b, a, true),
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
    fn decide_unsigned_upper_bound_by_signed_order(
        &self,
        term: &Bitvector32Term,
        bound: u32,
    ) -> Option<bool> {
        let nonnegative = self.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            term.clone(),
        ));
        if nonnegative == Some(false) {
            return Some(false);
        }
        let below = self.decide(&ConditionTerm::signed_less_equal(
            term.clone(),
            Bitvector32Term::Constant(bound),
        ));
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
    fn rebuilt_offset_is_exact(
        &self,
        offset: &crate::kernel::PointerOffsetTerm,
        element_width: u32,
        byte_path: bool,
    ) -> bool {
        use crate::kernel::PointerOffsetTerm;
        let rebuild = |offset: &PointerOffsetTerm| {
            if byte_path {
                byte_offset_from_pointer_offset(offset)
            } else {
                crate::kernel::reasoning::element_index_from_offset(offset, element_width)
            }
        };
        match offset {
            PointerOffsetTerm::Constant(_) => true,
            // Full-width constants or checked unsigned bounds make the
            // element projection exact. The byte projection below still
            // requires a constant whose scaled byte displacement fits.
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                if !byte_path && *byte_width != i64::from(element_width) {
                    return false;
                }
                if byte_path && *byte_width == 0 {
                    return true;
                }
                if !byte_path {
                    return crate::kernel::reasoning::element_index_from_offset_with_facts(
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
                let Some(value) = crate::kernel::assumptions::exact_sixty_four_bit_constant(
                    value, *unsigned, self,
                ) else {
                    return false;
                };
                value
                    .checked_mul(*byte_width)
                    .is_some_and(|bytes| i32::try_from(bytes).is_ok())
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                if !byte_path || *byte_width <= 1 {
                    return true;
                }
                let Ok(width) = u32::try_from(*byte_width) else {
                    return false;
                };
                self.decide(&ConditionTerm::signed_multiply_overflows(
                    value.as_ref().clone(),
                    Bitvector32Term::Constant(width),
                )) == Some(false)
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
                    (Some(left), Some(right)) => {
                        self.decide(&ConditionTerm::signed_add_overflows(left, right))
                            == Some(false)
                    }
                    _ => false,
                }
            }
            PointerOffsetTerm::Variable(_) => false,
        }
    }
}

thread_local! {
    static ORDER_WALK_INDEX_MEMO: std::cell::RefCell<
        std::collections::HashMap<u64, std::rc::Rc<OrderWalkIndex>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

const ORDER_WALK_INDEX_MEMO_LIMIT: usize = 20_000;

/// One state of the memory-resolution order walk: a term and whether the
/// path to it was strict.
type OrderReachState = (Bitvector32Term, bool);

/// The walks one [`OrderReachMemo`] entry serves: those over one fact set
/// toward one target, with one strictness requirement.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OrderReachKey {
    facts: u64,
    target: Bitvector32Term,
    require_strict: bool,
}

/// Whether a walk state reaches one that passes the target test.
///
/// The walk ([`PureFactContext::has_order_path_for_memory_resolution`])
/// answers whether some state it can reach from its source passes the test,
/// so the answer for a state is a property of that state, the fact set and
/// the target, never of the source a walk started from. A store to `a[cj]`
/// beside earlier cells `a[ci]` under a chain `c0 < c1 < … < n` asks
/// `ci < cj` of every cell, and each walk used to climb the chain from `ci`
/// to `cj` afresh, so the store cost the square of the chain and the line
/// its cube. Filed here, the first walk leaves every state on its path, and
/// the next one stops at its first step.
///
/// A success records the states on the path to the passing state; a
/// refusal records every state it reached, and only when no cycle cut or
/// limit touched it. Only walks that expanded no state reading memory record
/// anything, and only toward a target that reads none, over a fact set none
/// of whose unfiled order edges reads any ([`PureFactContext::order_reach_key`]):
/// there every test the walk applies is a question about the fact set, so a
/// recorded answer is the one exploring again would give. As for the
/// resolution memo, a success is found evidence and is kept however the
/// search was pruned, and a refusal only when no cycle cut or limit touched
/// the walk. Strictness only
/// ever grows along a path and a strict path passes every test a non-strict
/// one passes, so a state known to succeed without strictness succeeds with
/// it, and one known to fail with it fails without.
struct OrderReachMemo {
    entries:
        std::collections::HashMap<OrderReachKey, std::collections::HashMap<OrderReachState, bool>>,
    states: usize,
}

thread_local! {
    static ORDER_REACH_MEMO: std::cell::RefCell<OrderReachMemo> = std::cell::RefCell::new(OrderReachMemo {
        entries: std::collections::HashMap::new(),
        states: 0,
    });
}

const ORDER_REACH_MEMO_LIMIT: usize = 200_000;

fn order_reach_lookup(key: &OrderReachKey, term: &Bitvector32Term, strict: bool) -> Option<bool> {
    crate::instrumentation::record_deterministic_work(1);
    ORDER_REACH_MEMO.with(|memo| {
        let memo = memo.borrow();
        let states = memo.entries.get(key)?;
        let known = |strict: bool| states.get(&(term.clone(), strict)).copied();
        match (known(strict), strict) {
            (Some(answer), _) => Some(answer),
            (None, true) => known(false).filter(|reaches| *reaches),
            (None, false) => known(true).filter(|reaches| !*reaches),
        }
    })
}

fn record_order_reach_states(
    key: &OrderReachKey,
    states: impl IntoIterator<Item = OrderReachState>,
    reaches: bool,
) {
    ORDER_REACH_MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.states >= ORDER_REACH_MEMO_LIMIT {
            memo.entries.clear();
            memo.states = 0;
        }
        let entry = memo.entries.entry(key.clone()).or_default();
        let before = entry.len();
        for state in states {
            entry.insert(state, reaches);
        }
        let added = entry.len() - before;
        memo.states += added;
    });
}

/// Records that `reached` and every state on the walk's path to it reach a
/// state passing the target test.
fn record_order_reach_path(
    key: &OrderReachKey,
    parents: &BTreeMap<OrderReachState, OrderReachState>,
    reached: OrderReachState,
) {
    let mut path = vec![reached];
    while let Some(parent) = parents.get(path.last().expect("the path is never empty")) {
        path.push(parent.clone());
    }
    record_order_reach_states(key, path, true);
}

/// Records that no state a complete refusal reached reaches one passing
/// the target test.
fn record_order_reach_refusal(key: &OrderReachKey, seen: BTreeSet<OrderReachState>) {
    record_order_reach_states(key, seen, false);
}

/// One fact set's order edges and true `int32` equalities, filed for the
/// memory-resolution order walk
/// ([`PureFactContext::has_order_path_for_memory_resolution`]).
///
/// That walk used to compare every node it reached with every order fact and
/// every condition fact of the context, so each question cost the whole
/// context. A store to `a[c5]` beside earlier cells `a[ci]` and bounds
/// `0 <= ci < n` asks `c5 < ci` and `ci < c5` of every cell it keeps or
/// drops; each walk reaches `n` and scanned every bound at both nodes, so
/// `N` such stores cost `N^2`.
///
/// The filing is a pure syntactic function of the fact set, shared by
/// fact-set identity. It decides nothing: a node reads a superset of the
/// facts that could match it and applies the unchanged tests to each, in
/// fact order, so the walk's answer is the one the full scan gives.
pub(in crate::kernel) struct OrderWalkIndex {
    /// [`PureFactContext::condition_order_facts`], in its order.
    facts: std::rc::Rc<Vec<super::bounds::OrderFact>>,
    /// Edges whose lower endpoint is a constant or a variable that cannot
    /// name a load, by that endpoint and by its canonical form.
    by_lower: BTreeMap<Bitvector32Term, Vec<usize>>,
    /// Every other edge, ascending: read at every node.
    open: Vec<usize>,
    /// Whether no open edge's lower endpoint reads memory, so that the
    /// walk's tests against those edges are questions about the fact set
    /// alone (see `PureFactContext::order_reach_key`).
    open_memory_free: bool,
    /// The keyable-lower edges by their lower endpoint's exact constant.
    by_exact_constant: BTreeMap<i64, Vec<usize>>,
    /// The edges whose lower endpoint is a written constant, by its signed
    /// value.
    by_written_constant: BTreeMap<i64, Vec<usize>>,
    /// The keyable-lower edges whose lower endpoint an offset equality
    /// scales.
    offset_equality_lowers: Vec<usize>,
    /// The true `int32` equalities, in fact order, as `(left, right)`.
    equalities: Vec<(Bitvector32Term, Bitvector32Term)>,
    /// The equalities with a side that is a constant or a variable that
    /// cannot name a load, by that side, ascending.
    equalities_by_side: BTreeMap<Bitvector32Term, Vec<usize>>,
    /// The terms a true offset equality scales on one of its sides. A node
    /// among them can equal an endpoint through that fact alone.
    offset_equality_atoms: BTreeSet<Bitvector32Term>,
}

/// A variable the kernel never gives a load view: its id lies outside the
/// reserved load-variable space.
fn order_walk_plain_variable(term: &Bitvector32Term) -> bool {
    matches!(term, Bitvector32Term::Variable(variable)
        if !crate::kernel::eval::is_load_variable(variable))
}

/// Whether a term is integer arithmetic over constants and variables the
/// kernel never gives a load view: no load, no load variable, no pointer,
/// no fold, no application, no conditional, no float. What the order walk
/// learns about such terms depends on the fact set alone.
fn order_reach_memory_free(term: &Bitvector32Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        match term {
            Bitvector32Term::Constant(_)
            | Bitvector32Term::Int64Constant(_)
            | Bitvector32Term::UInt64Constant(_) => {}
            Bitvector32Term::Variable(_) => {
                if !order_walk_plain_variable(term) {
                    return false;
                }
            }
            crate::kernel::binary_machine_term!(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::BitwiseNot(value)
            | Bitvector32Term::Int64From32(value)
            | Bitvector32Term::UInt64From32(value)
            | Bitvector32Term::UInt32From64(value)
            | Bitvector32Term::Int64FromUInt32(value)
            | Bitvector32Term::UInt64FromInt32(value)
            | Bitvector32Term::UInt64FromInt64(value)
            | Bitvector32Term::Int64BitwiseNot(value)
            | Bitvector32Term::UInt64BitwiseNot(value) => pending.push(value),
            _ => return false,
        }
    }
    true
}

/// A variable the kernel never gives a load view, or its sign-bit flip
/// `v ^ 2^31`: the operand spelling of a 32-bit unsigned order
/// (`ConditionTerm::unsigned_less_than`). The walk's edge test between two
/// such terms, or one and a constant, has the routes it has for two plain
/// variables -- structural identity, exact constants, the trusted equality
/// graph, an exact offset equality -- since a flip is neither a load nor a
/// sum, so a flipped node reads its filed edges as a plain variable does.
fn order_walk_atom(term: &Bitvector32Term) -> bool {
    if let Bitvector32Term::BitwiseXor(left, right) = term {
        return match (left.as_ref(), right.as_ref()) {
            (Bitvector32Term::Constant(0x8000_0000), operand)
            | (operand, Bitvector32Term::Constant(0x8000_0000)) => {
                order_walk_plain_variable(operand)
            }
            _ => false,
        };
    }
    order_walk_plain_variable(term)
}

/// A lower endpoint the walk files by its own spelling: a constant, or an
/// [`order_walk_atom`].
fn order_walk_keyable(term: &Bitvector32Term) -> bool {
    matches!(term, Bitvector32Term::Constant(_)) || order_walk_atom(term)
}

#[cfg(test)]
thread_local! {
    static ORDER_WALK_FULL_SCAN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `body` with the order walk reading every fact at every node, as it
/// did before [`OrderWalkIndex`]: the reference the filed walk is checked
/// against.
#[cfg(test)]
pub(in crate::kernel) fn with_order_walk_full_scan<R>(body: impl FnOnce() -> R) -> R {
    let previous = ORDER_WALK_FULL_SCAN.with(|flag| flag.replace(true));
    let result = body();
    ORDER_WALK_FULL_SCAN.with(|flag| flag.set(previous));
    result
}

#[cfg(test)]
fn order_walk_full_scan_forced() -> bool {
    ORDER_WALK_FULL_SCAN.with(std::cell::Cell::get)
}

#[cfg(not(test))]
fn order_walk_full_scan_forced() -> bool {
    false
}

pub(in crate::kernel) fn condition_as_uint64_order_fact(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    let (left, right, lower_first, strict) = match condition {
        ConditionTerm::Bitvector64UnsignedLessThan(a, b) => (a, b, true, true),
        ConditionTerm::Bitvector64UnsignedLessEqual(a, b) => (a, b, true, false),
        ConditionTerm::Bitvector64UnsignedGreaterThan(a, b) => (a, b, false, true),
        ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b) => (a, b, false, false),
        _ => return None,
    };
    let (lower, upper) = if lower_first {
        (left.as_ref().clone(), right.as_ref().clone())
    } else {
        (right.as_ref().clone(), left.as_ref().clone())
    };
    Some(if value {
        (lower, upper, strict)
    } else {
        (upper, lower, !strict)
    })
}

/// A 64-bit order fact of one kind as `(lower, upper, strict)`: an unsigned
/// `uint64` comparison when `unsigned`, a signed `int64` one otherwise.
pub(in crate::kernel) fn wide_order_fact(
    condition: &ConditionTerm,
    value: bool,
    unsigned: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    if unsigned {
        condition_as_uint64_order_fact(condition, value)
    } else {
        crate::kernel::reasoning::order_reasoning::condition_as_int64_order_fact(condition, value)
    }
}

impl PureFactContext {
    /// Check the full unsigned value's range through its own bound index.
    /// This proves that taking its low word preserves its nonnegative signed
    /// value; a bound on the low word alone supplies no evidence here.
    pub(in crate::kernel) fn uint64_index_fits_int32(&self, term: &Bitvector32Term) -> bool {
        let guard = ConditionTerm::uint64_less_equal(
            term.clone(),
            Bitvector32Term::UInt64Constant(i32::MAX as u64),
        );
        if guard.reflexive_value() == Some(true)
            || self.exact_condition_value(&guard) == Some(true)
            || self.decide_uint64_constant_order_bounds_inner(&guard, true) == Some(true)
        {
            return true;
        }
        // `x - c` for a constant `c` fits where `x` does and the
        // difference does not wrap, `c <= x`. Both are 64-bit facts about
        // `x` itself.
        if let Bitvector32Term::UInt64Subtract(minuend, subtrahend) = term
            && subtrahend.uint64_as_const().is_some()
        {
            return self.uint64_index_fits_int32(minuend)
                && self.decide(&ConditionTerm::uint64_less_equal(
                    subtrahend.as_ref().clone(),
                    minuend.as_ref().clone(),
                )) == Some(true);
        }
        false
    }

    /// The signed counterpart: the full signed value lies in `0..=INT_MAX`,
    /// by 64-bit signed order facts on the value itself, so its low word is
    /// the value.
    pub(in crate::kernel) fn int64_index_fits_int32(&self, term: &Bitvector32Term) -> bool {
        self.decide(&ConditionTerm::int64_signed_less_equal(
            Bitvector32Term::Int64Constant(0),
            term.clone(),
        )) == Some(true)
            && self.decide(&ConditionTerm::int64_signed_less_equal(
                term.clone(),
                Bitvector32Term::Int64Constant(i32::MAX as i64),
            )) == Some(true)
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
        type Signed = fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm;
        let (left, right, signed): (_, _, Signed) = match condition {
            ConditionTerm::Bitvector64UnsignedLessThan(a, b) => {
                (a, b, ConditionTerm::int64_signed_less_than)
            }
            ConditionTerm::Bitvector64UnsignedLessEqual(a, b) => {
                (a, b, ConditionTerm::int64_signed_less_equal)
            }
            ConditionTerm::Bitvector64UnsignedGreaterThan(a, b) => {
                (a, b, ConditionTerm::int64_signed_greater_than)
            }
            ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b) => {
                (a, b, ConditionTerm::int64_signed_greater_equal)
            }
            _ => return None,
        };
        let reinterpreted = |term: &Bitvector32Term| match term {
            Bitvector32Term::UInt64FromInt64(value) => Some(value.as_ref().clone()),
            _ => None,
        };
        if reinterpreted(left).is_none() && reinterpreted(right).is_none() {
            return None;
        }
        let as_signed = |term: &Bitvector32Term| {
            if let Some(value) = reinterpreted(term) {
                let nonnegative = self.decide(&ConditionTerm::int64_signed_less_equal(
                    Bitvector32Term::Int64Constant(0),
                    value.clone(),
                )) == Some(true);
                return nonnegative.then_some(value);
            }
            let constant = i64::try_from(term.uint64_as_const()?).ok()?;
            Some(Bitvector32Term::Int64Constant(constant))
        };
        let left = as_signed(left)?;
        let right = as_signed(right)?;
        self.decide(&signed(left, right))
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
        let (left, right, mut operator) = match condition {
            ConditionTerm::Bitvector64UnsignedLessThan(a, b) => (a, b, 0),
            ConditionTerm::Bitvector64UnsignedLessEqual(a, b) => (a, b, 1),
            ConditionTerm::Bitvector64UnsignedGreaterThan(a, b) => (a, b, 2),
            ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b) => (a, b, 3),
            ConditionTerm::Bitvector64Equal(a, b) => (a, b, 4),
            _ => return None,
        };
        let (term, limit) = if let Some(limit) = right.uint64_as_const() {
            (left.as_ref(), limit)
        } else {
            let limit = left.uint64_as_const()?;
            operator = match operator {
                0 => 2,
                1 => 3,
                2 => 0,
                3 => 1,
                _ => 4,
            };
            (right.as_ref(), limit)
        };
        let bounds = self.uint64_order_bounds.get(term)?;
        for (endpoint, other, strict, upper) in bounds.keys() {
            crate::instrumentation::record_deterministic_work(1);
            let bound = if literal_only {
                other.uint64_as_const()
            } else {
                self.wide_constant_from_equalities(other)
            };
            let Some(bound) = bound else {
                continue;
            };
            let bound = if *strict {
                if *upper {
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
            let answer = match (operator, *upper) {
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
            let (a, b) = if *upper {
                (endpoint.clone(), other.clone())
            } else {
                (other.clone(), endpoint.clone())
            };
            // The index normalizes negated/reversed comparisons. Recover an
            // actual source fact through four exact lookups so expansion cites
            // the premise that was held, including its original truth value.
            let candidates = if *strict {
                [
                    (ConditionTerm::uint64_less_than(a.clone(), b.clone()), true),
                    (
                        ConditionTerm::uint64_greater_than(b.clone(), a.clone()),
                        true,
                    ),
                    (
                        ConditionTerm::uint64_greater_equal(a.clone(), b.clone()),
                        false,
                    ),
                    (ConditionTerm::uint64_less_equal(b, a), false),
                ]
            } else {
                [
                    (ConditionTerm::uint64_less_equal(a.clone(), b.clone()), true),
                    (
                        ConditionTerm::uint64_greater_equal(b.clone(), a.clone()),
                        true,
                    ),
                    (
                        ConditionTerm::uint64_greater_than(a.clone(), b.clone()),
                        false,
                    ),
                    (ConditionTerm::uint64_less_than(b, a), false),
                ]
            };
            if candidates
                .iter()
                .any(|(fact, value)| self.exact_condition_value(fact) == Some(*value))
            {
                return Some(answer);
            }
        }
        None
    }

    /// Follow only upper edges in the operand's indexed uint64 order graph.
    /// Each node is visited once; unrelated facts are never read.
    fn uint64_small_upper_bound(&self, term: &Bitvector32Term) -> Option<u64> {
        let mut stack = vec![crate::kernel::eval::canonical_term(term)];
        let mut seen = BTreeSet::new();
        let mut best = None;
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(value) = self.wide_constant_from_equalities(&term) {
                best = Some(best.map_or(value, |old: u64| old.min(value)));
                continue;
            }
            if let Some(edges) = self.uint64_order_bounds.get(&term) {
                for (_, upper, strict, forward) in edges.keys() {
                    crate::instrumentation::record_deterministic_work(1);
                    if !forward {
                        continue;
                    }
                    if let Some(value) = self.wide_constant_from_equalities(upper) {
                        if let Some(value) = if *strict {
                            value.checked_sub(1)
                        } else {
                            Some(value)
                        } {
                            best = Some(best.map_or(value, |old: u64| old.min(value)));
                        }
                    } else {
                        stack.push(crate::kernel::eval::canonical_term(upper));
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
    fn wide_order_chain(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        unsigned: bool,
    ) -> Option<bool> {
        let literal = |term: &Bitvector32Term| {
            term.uint64_as_const().is_some() || term.int64_as_const().is_some()
        };
        let lower = crate::kernel::eval::canonical_term(lower);
        let upper = crate::kernel::eval::canonical_term(upper);
        let upward = !literal(&lower);
        let (start, goal) = if upward {
            (lower, upper)
        } else {
            (upper, lower)
        };
        // Only the edges leaving a term in the walk's direction are read.
        let index = &self.wide_order_edges[usize::from(!unsigned)][usize::from(!upward)];
        let goal_constant = self.wide_constant_from_equalities(&goal);
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
                self.wide_constant_from_equalities(&term)
                    .zip(goal_constant)
                    .and_then(|(value, goal)| match toward_goal(value, goal) {
                        std::cmp::Ordering::Less => Some(true),
                        std::cmp::Ordering::Equal => Some(strict_so_far),
                        std::cmp::Ordering::Greater => None,
                    })
                    .or_else(|| {
                        // Every uint64 value is >= 0. The selected downward
                        // chain can end here without a stated 0<=term edge.
                        // Unknown values supply no strictness: it still comes
                        // only from a held edge. Known constants above retain
                        // their stronger intrinsic strict comparison.
                        (unsigned && !upward && goal_constant == Some(0)).then_some(strict_so_far)
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
            let Some(edges) = index.get(&term) else {
                continue;
            };
            for (other, strict) in edges.keys() {
                crate::instrumentation::record_deterministic_work(1);
                stack.push((other.clone(), strict_so_far || *strict));
            }
        }
        chained
    }

    /// Decide a 64-bit order comparison from a chain of held order facts of
    /// its own kind, signed or unsigned: transitivity, a constant bound
    /// reached through a chain, and `a <= b` with `a != b`. The reversed
    /// chain refutes: `b <= a` refutes `a < b`, and `b < a` refutes `a <= b`.
    pub(super) fn decide_wide_order_chain(&self, condition: &ConditionTerm) -> Option<bool> {
        let (lower, upper, strict, unsigned) = match condition_as_uint64_order_fact(condition, true)
        {
            Some((lower, upper, strict)) => (lower, upper, strict, true),
            None => {
                let (lower, upper, strict) = condition_as_int64_order_fact(condition, true)?;
                (lower, upper, strict, false)
            }
        };
        // An unsigned value held unequal to zero is at least one.
        if unsigned
            && matches!(
                (lower.uint64_as_const(), strict),
                (Some(0), true) | (Some(1), false)
            )
            && [
                ConditionTerm::uint64_equal(upper.clone(), Bitvector32Term::UInt64Constant(0)),
                ConditionTerm::uint64_equal(Bitvector32Term::UInt64Constant(0), upper.clone()),
            ]
            .iter()
            .any(|zero| self.exact_condition_value(zero) == Some(false))
        {
            return Some(true);
        }
        match self.wide_order_chain(&lower, &upper, unsigned) {
            Some(true) => return Some(true),
            Some(false) if !strict => return Some(true),
            Some(false) => {
                let equal = ConditionTerm::int64_equal(lower.clone(), upper.clone());
                if self.exact_condition_value(&equal) == Some(false)
                    || self.exact_condition_value(&ConditionTerm::int64_equal(
                        upper.clone(),
                        lower.clone(),
                    )) == Some(false)
                {
                    return Some(true);
                }
            }
            None => {}
        }
        match self.wide_order_chain(&upper, &lower, unsigned) {
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
        if let Some((left, right, strict)) = condition_as_uint64_order_fact(condition, true) {
            let left = crate::kernel::eval::canonical_term(&left);
            let right = crate::kernel::eval::canonical_term(&right);
            if let Some(bounds) = self.uint64_order_bounds.get(&left) {
                for (_, other, held_strict, forward) in bounds.keys() {
                    crate::instrumentation::record_deterministic_work(1);
                    if crate::kernel::eval::canonical_term(other) != right {
                        continue;
                    }
                    if *forward && (!strict || *held_strict) {
                        return Some(true);
                    }
                    if !*forward && (strict || *held_strict) {
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
        if let ConditionTerm::Bitvector64UnsignedLessEqual(left, right) = condition {
            let limit = right.uint64_as_const()?;
            if self.uint64_small_upper_bound(left)? <= limit {
                return Some(true);
            }
            return None;
        }
        if let Some(guards) = condition.nonnegative_division_bound_guards()
            && guards.iter().all(|guard| self.decide(guard) == Some(true))
        {
            return Some(true);
        }
        let (left, right, strict) = condition_as_order_fact(condition, true)?;
        let small = |term: &Bitvector32Term| match term {
            Bitvector32Term::Constant(value) if *value <= i32::MAX as u32 => Some(*value as u64),
            _ => None,
        };
        // Truncation commutes with addition modulo 2^32, so a truncated
        // term plus a constant is the truncation of the 64-bit sum, signed
        // or unsigned. The range check below is made on that sum.
        let truncated = |term: &Bitvector32Term, unsigned: bool| match term {
            Bitvector32Term::UInt32From64(value) => Some(value.as_ref().clone()),
            Bitvector32Term::Add(left, right) => {
                let (value, constant) = match (left.as_ref(), right.as_ref()) {
                    (Bitvector32Term::UInt32From64(value), constant)
                    | (constant, Bitvector32Term::UInt32From64(value)) => (value, small(constant)?),
                    _ => return None,
                };
                Some(if unsigned {
                    Bitvector32Term::uint64_add(
                        value.as_ref().clone(),
                        Bitvector32Term::UInt64Constant(constant),
                    )
                } else {
                    Bitvector32Term::int64_add(
                        value.as_ref().clone(),
                        Bitvector32Term::Int64Constant(constant as i64),
                    )
                })
            }
            _ => None,
        };
        if truncated(&left, true).is_none() && truncated(&right, true).is_none() {
            return None;
        }
        let wide = |term: &Bitvector32Term, unsigned: bool| {
            truncated(term, unsigned).or_else(|| {
                small(term).map(|value| {
                    if unsigned {
                        Bitvector32Term::UInt64Constant(value)
                    } else {
                        Bitvector32Term::Int64Constant(value as i64)
                    }
                })
            })
        };
        // Read as unsigned values: both at most `INT_MAX`.
        let a = wide(&left, true)?;
        let b = wide(&right, true)?;
        let unsigned_small = |term: &Bitvector32Term| {
            self.uint64_small_upper_bound(term)
                .is_some_and(|bound| bound <= i32::MAX as u64)
        };
        if unsigned_small(&a) && unsigned_small(&b) {
            if a.uint64_as_const() == Some(0) && !strict {
                return Some(true);
            }
            let comparison = if strict {
                ConditionTerm::uint64_less_than(a, b)
            } else {
                ConditionTerm::uint64_less_equal(a, b)
            };
            return self.decide(&comparison);
        }
        // Read as signed values: both in `0..=INT_MAX`, where the low word
        // is the value and the two readings of the order agree.
        let a = wide(&left, false)?;
        let b = wide(&right, false)?;
        let signed_small = |term: &Bitvector32Term| {
            self.wide_order_chain(&Bitvector32Term::Int64Constant(0), term, false)
                .is_some()
                && self
                    .wide_order_chain(
                        term,
                        &Bitvector32Term::Int64Constant(i32::MAX as i64),
                        false,
                    )
                    .is_some()
        };
        if !signed_small(&a) || !signed_small(&b) {
            return None;
        }
        let comparison = if strict {
            ConditionTerm::int64_signed_less_than(a, b)
        } else {
            ConditionTerm::int64_signed_less_equal(a, b)
        };
        self.decide(&comparison)
    }
}

#[cfg(test)]
mod slice_index_tests {
    use super::*;

    #[test]
    fn unsigned_zero_endpoint_joins_only_selected_strict_order_paths() {
        let value = |id| Bitvector32Term::Variable(Variable(id));
        let zero = Bitvector32Term::UInt64Constant(0);
        let index = value(997_910);
        let count = value(997_911);
        let limit = Bitvector32Term::UInt64Constant(i64::MAX as u64 / 4);
        let mut work = Vec::new();
        for unrelated in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut context = PureFactContext::new();
            for id in 0..unrelated {
                context = context.assume_condition(
                    ConditionTerm::uint64_less_than(value(998_100 + id), value(999_200 + id)),
                    true,
                );
            }
            context = context
                .assume_condition(
                    ConditionTerm::uint64_less_than(index.clone(), count.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::uint64_less_equal(count.clone(), limit.clone()),
                    true,
                );
            let (answers, measured) = crate::instrumentation::measure_deterministic_work(|| {
                [
                    context.decide(&ConditionTerm::uint64_less_than(
                        zero.clone(),
                        count.clone(),
                    )),
                    context.decide(&ConditionTerm::uint64_less_equal(
                        index.clone(),
                        count.clone(),
                    )),
                    context.decide(&ConditionTerm::uint64_less_equal(
                        count.clone(),
                        limit.clone(),
                    )),
                ]
            });
            assert_eq!(answers, [Some(true); 3]);
            work.push(measured);
        }
        assert!(work.windows(2).all(|pair| pair[0] == pair[1]), "{work:?}");
        let possible_zero = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_less_equal(index.clone(), count.clone()),
            true,
        );
        assert_eq!(
            possible_zero.decide(&ConditionTerm::uint64_less_than(
                zero.clone(),
                count.clone()
            )),
            None
        );
        let positive_constant = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_less_equal(Bitvector32Term::UInt64Constant(1), count.clone()),
            true,
        );
        assert_eq!(
            positive_constant.decide(&ConditionTerm::uint64_less_than(
                zero.clone(),
                count.clone()
            )),
            Some(true)
        );
        assert_eq!(
            PureFactContext::new().decide(&ConditionTerm::uint64_less_equal(zero, count.clone())),
            Some(true)
        );
        let signed = PureFactContext::new().assume_condition(
            ConditionTerm::int64_signed_less_than(index.clone(), count.clone()),
            true,
        );
        assert_eq!(
            signed.decide(&ConditionTerm::int64_signed_less_than(
                Bitvector32Term::Int64Constant(0),
                count
            )),
            None
        );
    }

    #[test]
    fn wide_order_chains_decide_by_kind_and_refute_by_the_reversed_chain() {
        let v = |n: u64| Bitvector32Term::Variable(Variable(997000 + n));
        let (a, b, c, d) = (v(0), v(1), v(2), v(3));
        type Order = fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm;
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
        let a = Bitvector32Term::Variable(Variable(997100));
        let b = Bitvector32Term::Variable(Variable(997101));
        let u = Bitvector32Term::UInt64Constant;
        let unsigned = PureFactContext::new()
            .assume_condition(ConditionTerm::uint64_less_than(a.clone(), b.clone()), true)
            .assume_condition(ConditionTerm::uint64_less_equal(b.clone(), u(10)), true)
            .assume_condition(ConditionTerm::uint64_less_equal(u(5), a.clone()), true);
        let lt = ConditionTerm::uint64_less_than;
        let le = ConditionTerm::uint64_less_equal;
        assert_eq!(unsigned.decide(&lt(a.clone(), u(10))), Some(true));
        assert_eq!(unsigned.decide(&le(a.clone(), u(9))), None);
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
    fn wide_order_chain_work_follows_the_chain_and_not_unrelated_facts() {
        let v = |n: u64| Bitvector32Term::Variable(Variable(996000 + n));
        let lt = ConditionTerm::uint64_less_than;
        let u = Bitvector32Term::UInt64Constant;
        // A chain of fixed length beside a growing set of unrelated facts,
        // some sharing a literal endpoint with the question.
        let mut beside = Vec::new();
        for size in [8, 32, 128, 512] {
            let mut facts = PureFactContext::new();
            for i in 0..4 {
                facts = facts.assume_condition(lt(v(i), v(i + 1)), true);
            }
            facts = facts.assume_condition(lt(v(4), u(1000)), true);
            for i in 0..size {
                facts = facts
                    .assume_condition(lt(v(10_000 + i), v(20_000 + i)), true)
                    .assume_condition(lt(u(0), v(30_000 + i)), true)
                    .assume_condition(lt(v(40_000 + i), u(1000)), true);
            }
            let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
                [
                    facts.decide(&lt(v(0), v(4))),
                    facts.decide(&lt(v(0), u(1000))),
                    facts.decide(&lt(v(4), v(0))),
                ]
            });
            assert_eq!(answers, [Some(true), Some(true), Some(false)]);
            beside.push(work);
        }
        assert!(beside.iter().all(|work| *work == beside[0]), "{beside:?}");
        // A growing chain costs work linear in its length.
        let mut along = Vec::new();
        for size in [8u64, 16, 32, 64] {
            let mut facts = PureFactContext::new();
            for i in 0..size {
                facts = facts.assume_condition(lt(v(i), v(i + 1)), true);
            }
            let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.decide(&lt(v(0), v(size)))
            });
            assert_eq!(answer, Some(true));
            along.push(work);
        }
        for pair in along.windows(2) {
            assert!(pair[1] <= 3 * pair[0], "{along:?}");
        }
    }

    #[test]
    fn uint64_constant_order_strengthening_is_sound_at_full_width_and_scales() {
        let n = Bitvector32Term::Variable(Variable(998001));
        let c = Bitvector32Term::UInt64Constant;
        let mut work_counts = Vec::new();
        for size in [8, 32, 128, 512] {
            let mut facts = PureFactContext::new();
            for i in 0..size {
                // Shared endpoints exercise the dangerous constant-index shape.
                facts = facts.assume_condition(
                    ConditionTerm::uint64_less_than(
                        c(0),
                        Bitvector32Term::Variable(Variable(999000 + i)),
                    ),
                    true,
                );
            }
            facts = facts.assume_condition(
                ConditionTerm::uint64_greater_than(n.clone(), c(4294967295)),
                true,
            );
            let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
                [
                    facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(253))),
                    facts.decide(&ConditionTerm::uint64_less_equal(n.clone(), c(65535))),
                    facts.decide(&ConditionTerm::uint64_less_than(c(0), n.clone())),
                    facts.decide(&ConditionTerm::uint64_equal(n.clone(), c(0))),
                ]
            });
            assert_eq!(answers, [Some(false), Some(false), Some(true), Some(false)]);
            work_counts.push(work);
        }
        assert!(work_counts[0] > 0);
        assert!(
            work_counts.iter().all(|work| *work == work_counts[0]),
            "{work_counts:?}"
        );
        for bound in [
            0,
            253,
            65535,
            4294967295,
            i64::MAX as u64,
            i64::MAX as u64 + 1,
            u64::MAX,
        ] {
            let facts = PureFactContext::new()
                .assume_condition(ConditionTerm::uint64_less_equal(n.clone(), c(bound)), true);
            assert_eq!(
                facts.decide(&ConditionTerm::uint64_greater_than(n.clone(), c(bound))),
                Some(false)
            );
            if bound < u64::MAX {
                assert_eq!(
                    facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(bound + 1))),
                    Some(true)
                );
                assert_eq!(
                    facts.decide(&ConditionTerm::uint64_equal(n.clone(), c(bound + 1))),
                    Some(false)
                );
            }
            assert_ne!(
                facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(bound))),
                Some(true)
            );
        }
        let negative = PureFactContext::new()
            .assume_condition(ConditionTerm::uint64_less_equal(n.clone(), c(65535)), false);
        assert_eq!(
            negative.decide(&ConditionTerm::uint64_less_than(n.clone(), c(253))),
            Some(false)
        );
        assert_eq!(
            PureFactContext::new().decide(&ConditionTerm::uint64_less_than(n, c(253))),
            None
        );
    }

    #[test]
    fn uint64_constant_lower_bound_survives_checked_narrowing() {
        let value = Bitvector32Term::Variable(Variable(991003));
        let context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_than(Bitvector32Term::UInt64Constant(0), value.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    value.clone(),
                    Bitvector32Term::UInt64Constant(i32::MAX as u64),
                ),
                true,
            );
        let goal = ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            Bitvector32Term::uint32_from_64(value),
        );
        assert_eq!(context.decide_condition_for_simp(&goal), Some(true));
    }

    #[test]
    fn uint64_slice_remainder_bounds_ignore_unrelated_facts() {
        let length = Bitvector32Term::Variable(Variable(993001));
        let midpoint = Bitvector32Term::Variable(Variable(993002));
        let difference = Bitvector32Term::uint64_subtract(length.clone(), midpoint.clone());
        let positive =
            ConditionTerm::uint64_less_than(Bitvector32Term::UInt64Constant(0), difference.clone());
        let bounded = ConditionTerm::uint64_less_equal(difference, length.clone());
        let mut work = Vec::new();
        for size in [8, 32, 128, 512] {
            let mut context = PureFactContext::new();
            for n in 0..size {
                context = context.assume_condition(
                    ConditionTerm::uint64_less_equal(
                        Bitvector32Term::Variable(Variable(994000 + n)),
                        Bitvector32Term::UInt64Constant(100),
                    ),
                    true,
                );
            }
            context = context.assume_condition(
                ConditionTerm::uint64_less_than(midpoint.clone(), length.clone()),
                true,
            );
            let (_, used) = crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(context.decide_condition_for_simp(&positive), Some(true));
                assert_eq!(context.decide_condition_for_simp(&bounded), Some(true));
            });
            work.push(used);
        }
        assert!(work.iter().all(|used| *used == work[0]), "{work:?}");
        let unbounded = PureFactContext::new();
        assert_ne!(unbounded.decide_condition_for_simp(&positive), Some(true));
        assert_ne!(unbounded.decide_condition_for_simp(&bounded), Some(true));
        let underflow = PureFactContext::new()
            .assume_condition(ConditionTerm::uint64_greater_than(midpoint, length), true);
        assert_ne!(underflow.decide_condition_for_simp(&bounded), Some(true));
    }

    #[test]
    fn uint64_slice_index_transport_is_sound_and_ignores_unrelated_bounds() {
        let index = Bitvector32Term::Variable(Variable(991001));
        let length = Bitvector32Term::Variable(Variable(991002));
        let index_word = Bitvector32Term::uint32_from_64(index.clone());
        let length_word = Bitvector32Term::uint32_from_64(length.clone());
        let goal = ConditionTerm::signed_less_than(index_word.clone(), length_word);
        let mut work = Vec::new();
        for size in [8, 32, 128, 512] {
            let mut context = PureFactContext::new();
            for n in 0..size {
                context = context.assume_condition(
                    ConditionTerm::uint64_less_equal(
                        Bitvector32Term::Variable(Variable(992000 + n)),
                        Bitvector32Term::UInt64Constant(100),
                    ),
                    true,
                );
            }
            context = context
                .assume_condition(
                    ConditionTerm::uint64_less_than(index.clone(), length.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::uint64_less_equal(
                        length.clone(),
                        Bitvector32Term::UInt64Constant(i32::MAX as u64),
                    ),
                    true,
                );
            let (_, used) = crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(context.decide_small_uint64_index_order(&goal), Some(true));
                assert_eq!(
                    context.decide_small_uint64_index_order(&ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        index_word.clone()
                    )),
                    Some(true)
                );
            });
            work.push(used);
        }
        assert!(work.iter().all(|used| *used == work[0]), "{work:?}");
        let unbounded = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_less_than(index.clone(), length.clone()),
            true,
        );
        assert_eq!(unbounded.decide_small_uint64_index_order(&goal), None);
        let high = unbounded.assume_condition(
            ConditionTerm::uint64_less_equal(length, Bitvector32Term::UInt64Constant(4294967296)),
            true,
        );
        assert_eq!(high.decide_small_uint64_index_order(&goal), None);
        let reversed = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    index.clone(),
                    Bitvector32Term::UInt64Constant(10),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    Bitvector32Term::Variable(Variable(991002)),
                    Bitvector32Term::UInt64Constant(10),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_greater_equal(
                    index,
                    Bitvector32Term::Variable(Variable(991002)),
                ),
                true,
            );
        assert_eq!(reversed.decide_small_uint64_index_order(&goal), Some(false));
    }
}
