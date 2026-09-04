use super::*;

impl PureFactContext {
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
        match condition {
            ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerEqual(left, right) => {
                if self.has_pointer_equality_path(left, right) {
                    Some(true)
                } else {
                    left.blocks_proven_distinct(right).then_some(false)
                }
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
                        let left_index = int32_element_index_from_offset(left);
                        let right_index = int32_element_index_from_offset(right);
                        match (left_index, right_index) {
                            (Some(left_index), Some(right_index)) => exact_or_unequal(
                                self.decide(&ConditionTerm::equal(left_index, right_index)),
                                self.rebuilt_offset_is_exact(left, false)
                                    && self.rebuilt_offset_is_exact(right, false),
                            ),
                            _ => {
                                let left_bytes = byte_offset_from_pointer_offset(left);
                                let right_bytes = byte_offset_from_pointer_offset(right);
                                match (left_bytes, right_bytes) {
                                    (Some(left_bytes), Some(right_bytes)) => exact_or_unequal(
                                        self.decide(&ConditionTerm::equal(left_bytes, right_bytes)),
                                        self.rebuilt_offset_is_exact(left, true)
                                            && self.rebuilt_offset_is_exact(right, true),
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

                if self.bitvector_terms_equal_from_facts(&left, &right)
                    || self
                        .has_condition_fact(ConditionTerm::equal(left.clone(), right.clone()), true)
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
                    None
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
                if right == signed_int_max_term() || left == signed_int_min_term() {
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
                {
                    Some(true)
                } else if self
                    .has_condition_fact(ConditionTerm::signed_greater_than(left, right), true)
                {
                    Some(false)
                } else {
                    None
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
                    None
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
                if right == signed_int_min_term() || left == signed_int_max_term() {
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
                    || self.order_facts_force_equal(&left, &right)
                {
                    Some(true)
                } else if self
                    .has_condition_fact(ConditionTerm::signed_less_than(left, right), true)
                {
                    Some(false)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn has_pointer_equality_path(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        let canonical_pointer =
            |pointer: &Pointer| crate::kernel::api::canonicalize_pointer_loads(pointer);
        let matches = |candidate: &Pointer, expected: &Pointer| {
            candidate == expected
                || candidate.block == expected.block
                    && canonical_pointer(candidate) == canonical_pointer(expected)
        };
        let offsets_match = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            canonical_pointer(&Pointer {
                block: PointerBlock::ExternalArgument,
                offset: left.clone(),
            }) == canonical_pointer(&Pointer {
                block: PointerBlock::ExternalArgument,
                offset: right.clone(),
            })
        };
        let translated = |goal_left: &Pointer,
                          goal_right: &Pointer,
                          fact_left: &Pointer,
                          fact_right: &Pointer| {
            goal_left.block == fact_left.block
                && goal_right.block == fact_right.block
                && pointer_offsets_have_same_advance(
                    &goal_left.offset,
                    &fact_left.offset,
                    &goal_right.offset,
                    &fact_right.offset,
                    self,
                )
        };
        if self.condition_facts.iter().any(|(condition, value)| {
            let ConditionTerm::PointerEqual(fact_left, fact_right) = condition else {
                return false;
            };
            *value
                && (translated(left, right, fact_left, fact_right)
                    || translated(left, right, fact_right, fact_left))
        }) {
            return true;
        }
        let mut seen = BTreeSet::from([left.clone()]);
        let mut frontier = vec![left.clone()];
        while let Some(current) = frontier.pop() {
            for (condition, value) in self.condition_facts.iter() {
                if !*value {
                    continue;
                }
                let next = match condition {
                    ConditionTerm::PointerEqual(edge_left, edge_right) => {
                        if matches(edge_left, &current) {
                            Some(edge_right.as_ref().clone())
                        } else if matches(edge_right, &current) {
                            Some(edge_left.as_ref().clone())
                        } else {
                            None
                        }
                    }
                    ConditionTerm::PointerOffsetEqual(edge_left, edge_right) => {
                        if offsets_match(edge_left, &current.offset) {
                            Some(Pointer {
                                block: current.block.clone(),
                                offset: edge_right.as_ref().clone(),
                            })
                        } else if offsets_match(edge_right, &current.offset) {
                            Some(Pointer {
                                block: current.block.clone(),
                                offset: edge_left.as_ref().clone(),
                            })
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                let Some(next) = next else {
                    continue;
                };
                if matches(&next, right) {
                    return true;
                }
                if seen.insert(next.clone()) {
                    frontier.push(next);
                }
            }
        }
        false
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
        let mut stack = vec![(left.clone(), false, Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far, path)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (current == *right || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
                && !path.is_empty()
            {
                return Some(path);
            }
            for edge in order_facts.iter().rev() {
                if current != edge.lower {
                    continue;
                }
                let mut extended = path.clone();
                extended.push(edge.clone());
                stack.push((edge.upper.clone(), strict_so_far || edge.strict, extended));
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

    pub(in crate::kernel) fn has_order_path_for_memory_resolution(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        let order_facts = self.condition_order_facts();
        let order_terms_match = |left: &Bitvector32Term, right: &Bitvector32Term| {
            if left == right {
                return true;
            }
            let (
                Bitvector32Term::MemoryLoad(left_memory, left_pointer),
                Bitvector32Term::MemoryLoad(right_memory, right_pointer),
            ) = (left, right)
            else {
                return false;
            };
            left_pointer == right_pointer
                && (memories_proven_equal_for_memory_resolution(left_memory, right_memory, self)
                    // Whole-memory equality fails across a call's havoc block
                    // even when the loaded cell is provably framed; the
                    // bounded per-load bridge accepts effect-summary framing
                    // for exactly this pointer.
                    || self.memory_snapshots_directly_proven_equal_for_memory_resolution(
                        left_memory,
                        right_memory,
                        left_pointer,
                    ))
        };
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if crate::instrumentation::deadline_exceeded() {
                return false;
            }
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
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
                return true;
            }
            for (edge_left, edge_right, edge_strict) in order_facts.iter() {
                if crate::instrumentation::deadline_exceeded() {
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
                    stack.push((
                        edge_right.clone(),
                        strict_so_far || *edge_strict || constant_connection == Some(true),
                    ));
                }
            }
            for (condition, value) in self.condition_facts.iter() {
                if crate::instrumentation::deadline_exceeded() {
                    return false;
                }
                let (ConditionTerm::Bitvector32Equal(left, right), true) = (condition, value)
                else {
                    continue;
                };
                if order_terms_match(&current, left) {
                    stack.push((right.as_ref().clone(), strict_so_far));
                }
                if order_terms_match(&current, right) {
                    stack.push((left.as_ref().clone(), strict_so_far));
                }
            }
        }
        false
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
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        condition_as_order_fact(condition, value).is_some_and(|(left, right, strict)| {
            let left = self.simplify_bitvector_under_assumptions(&left);
            let right = self.simplify_bitvector_under_assumptions(&right);
            self.has_order_path_for_memory_resolution(&left, &right, strict)
        })
    }
}

/// Whether both goal pointers advance their corresponding fact pointers by
/// the same exact offset. This is the pointer-congruence case needed by an
/// induction step such as `p == arr + i` followed by `p = p + 1` and
/// `i = i + 1`. Integer additions inside scaled offsets are distributed only
/// when their signed-overflow predicate is already known false; otherwise
/// exact pointer offsets must remain opaque.
fn pointer_offsets_have_same_advance(
    goal_left: &PointerOffsetTerm,
    fact_left: &PointerOffsetTerm,
    goal_right: &PointerOffsetTerm,
    fact_right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    let Some(left_delta) = pointer_offset_additive_delta(goal_left, fact_left, assumptions) else {
        return false;
    };
    let Some(right_delta) = pointer_offset_additive_delta(goal_right, fact_right, assumptions)
    else {
        return false;
    };
    left_delta == right_delta
}

fn pointer_offset_additive_delta(
    goal: &PointerOffsetTerm,
    fact: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<Vec<PointerOffsetTerm>> {
    let mut goal = pointer_offset_addends(goal, assumptions)?;
    for fact_addend in pointer_offset_addends(fact, assumptions)? {
        let index = goal
            .iter()
            .position(|addend| pointer_offset_addends_equal(addend, &fact_addend, assumptions))?;
        goal.remove(index);
    }
    Some(goal)
}

fn pointer_offset_addends_equal(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let (
        PointerOffsetTerm::Int32Scaled {
            value: left_value,
            byte_width: left_width,
        },
        PointerOffsetTerm::Int32Scaled {
            value: right_value,
            byte_width: right_width,
        },
    ) = (left, right)
    else {
        return false;
    };
    left_width == right_width
        && assumptions.decide(&ConditionTerm::equal(
            left_value.as_ref().clone(),
            right_value.as_ref().clone(),
        )) == Some(true)
}

fn pointer_offset_addends(
    offset: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<Vec<PointerOffsetTerm>> {
    match offset {
        PointerOffsetTerm::Constant(0) => Some(Vec::new()),
        PointerOffsetTerm::Add(left, right) => {
            let mut addends = pointer_offset_addends(left, assumptions)?;
            addends.extend(pointer_offset_addends(right, assumptions)?);
            Some(addends)
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } => match value.as_ref() {
            Bitvector32Term::Add(left, right)
                if assumptions.decide(&ConditionTerm::signed_add_overflows(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                )) == Some(false) =>
            {
                let left = PointerOffsetTerm::scale_int32(left.as_ref().clone(), *byte_width);
                let right = PointerOffsetTerm::scale_int32(right.as_ref().clone(), *byte_width);
                let mut addends = pointer_offset_addends(&left, assumptions)?;
                addends.extend(pointer_offset_addends(&right, assumptions)?);
                Some(addends)
            }
            _ => Some(vec![offset.clone()]),
        },
        _ => Some(vec![offset.clone()]),
    }
}

/// Splits both offsets into their addends and removes every addend they
/// share (one occurrence per match). Offsets are exact i64 sums of their
/// addends, so `C + L == C + R` holds exactly if and only if `L == R`.
fn cancel_common_offset_addends(
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
    /// Whether the index or byte term the offset rebuilders produce for
    /// `offset` denotes the exact offset rather than a wrapped 32-bit value.
    /// `PointerOffsetTerm` semantics are exact i64, so equal rebuilt terms
    /// imply equal offsets only when every rebuilt addition (and, on the byte
    /// path, every scaling by a width) is proved not to overflow under the
    /// current facts. Constants and single index terms are always exact.
    fn rebuilt_offset_is_exact(
        &self,
        offset: &crate::kernel::PointerOffsetTerm,
        byte_path: bool,
    ) -> bool {
        use crate::kernel::PointerOffsetTerm;
        let rebuild = |offset: &PointerOffsetTerm| {
            if byte_path {
                byte_offset_from_pointer_offset(offset)
            } else {
                int32_element_index_from_offset(offset)
            }
        };
        match offset {
            PointerOffsetTerm::Constant(_) => true,
            PointerOffsetTerm::Int32Scaled { value, byte_width }
            | PointerOffsetTerm::Int64Scaled {
                value, byte_width, ..
            } => {
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
                self.rebuilt_offset_is_exact(right, byte_path)
            }
            PointerOffsetTerm::Add(left, right)
                if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
            {
                self.rebuilt_offset_is_exact(left, byte_path)
            }
            PointerOffsetTerm::Add(left, right) => {
                if !(self.rebuilt_offset_is_exact(left, byte_path)
                    && self.rebuilt_offset_is_exact(right, byte_path))
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
