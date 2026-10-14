use super::*;

#[cfg(test)]
thread_local! {
    static SIGNED_INTERVAL_FALLBACK_FACT_VISITS: Cell<usize> = const { Cell::new(0) };
}

#[derive(Clone)]
struct SignedOrderBound {
    other: Bitvector32Term,
    strict: bool,
    upper: bool,
}

impl PureFactContext {
    #[cfg(test)]
    fn reset_signed_interval_fallback_fact_visits() {
        SIGNED_INTERVAL_FALLBACK_FACT_VISITS.with(|visits| visits.set(0));
    }

    #[cfg(test)]
    fn signed_interval_fallback_fact_visits() -> usize {
        SIGNED_INTERVAL_FALLBACK_FACT_VISITS.with(Cell::get)
    }

    fn exact_signed_order_bounds(&self, term: &Bitvector32Term) -> Option<Vec<SignedOrderBound>> {
        // The index keys endpoints by canonical form; canonicalize the query
        // so any term equal to the bounded value finds its bounds.
        let term = crate::kernel::eval::canonical_term(term);
        self.exact_signed_order_bounds_for_key(&term)
    }

    fn exact_signed_order_bounds_for_key(
        &self,
        term: &Bitvector32Term,
    ) -> Option<Vec<SignedOrderBound>> {
        self.signed_order_bounds.get(term).map(|bounds| {
            bounds
                .keys()
                .map(|(_, other, strict, upper)| SignedOrderBound {
                    other: other.clone(),
                    strict: *strict,
                    upper: *upper,
                })
                .collect()
        })
    }

    /// The range of `term` that its own recorded constant order bounds give,
    /// read from `signed_order_bounds` at the term's canonical form: one
    /// keyed lookup, no chain, no scan of the fact set. `None` when no
    /// constant bound is filed there. For a caller that runs per cell and
    /// may not search; [`Self::signed_interval`] is the complete answer.
    pub(in crate::kernel) fn indexed_constant_interval(
        &self,
        term: &Bitvector32Term,
    ) -> Option<(i64, i64)> {
        let mut lower = i64::from(i32::MIN);
        let mut upper = i64::from(i32::MAX);
        let mut bounded = false;
        for bound in self.exact_signed_order_bounds(term)? {
            crate::instrumentation::record_deterministic_work(1);
            let Some(value) = signed_bitvector_constant(&bound.other) else {
                continue;
            };
            bounded = true;
            match (bound.upper, bound.strict) {
                (true, true) => upper = upper.min(value - 1),
                (true, false) => upper = upper.min(value),
                (false, true) => lower = lower.max(value + 1),
                (false, false) => lower = lower.max(value),
            }
        }
        bounded.then_some((lower, upper))
    }

    /// The tightest constant bound on `term` that a chain of recorded int32
    /// order facts reaches: an upper bound (`upper`) from `term <= a < b <= c`
    /// ending at a constant, or a lower bound from a chain ending below
    /// `term`. A strict link anywhere on the chain tightens the constant by
    /// one, which is exact over the integers the int32 values denote.
    ///
    /// Every step is a keyed lookup in `signed_order_bounds` at the current
    /// node's canonical form, which files each fact under both endpoints, so
    /// the walk reads only the facts on chains out of `term` in the one
    /// direction asked, never an unrelated fact. Each `(node, strict)` state
    /// is expanded once, so the work is linear in the order facts of that
    /// component. A chain reaching a constant stops there: a constant's own
    /// bounds cannot tighten what it already bounds.
    fn chained_signed_constant_bound(&self, term: &Bitvector32Term, upper: bool) -> Option<i64> {
        let start = crate::kernel::eval::canonical_term(term);
        let mut best: Option<i64> = None;
        let mut stack = vec![(start, false)];
        let mut seen = BTreeSet::new();
        while let Some((node, strict_so_far)) = stack.pop() {
            if !seen.insert((node.clone(), strict_so_far)) {
                continue;
            }
            // A strict state reaches everything the non-strict state reaches
            // with bounds at least as tight, so the non-strict one adds
            // nothing once the strict one has been expanded.
            if !strict_so_far && seen.contains(&(node.clone(), true)) {
                continue;
            }
            let Some(bounds) = self.signed_order_bounds.get(&node) else {
                continue;
            };
            for (_, other, strict, own_is_lower) in bounds.keys() {
                crate::instrumentation::record_deterministic_work(1);
                if *own_is_lower != upper {
                    continue;
                }
                let strict = strict_so_far || *strict;
                if let Some(value) = signed_bitvector_constant(other) {
                    let candidate = match (upper, strict) {
                        (true, true) => value.checked_sub(1),
                        (false, true) => value.checked_add(1),
                        (_, false) => Some(value),
                    };
                    if let Some(candidate) = candidate {
                        best = Some(match (best, upper) {
                            (Some(best), true) => best.min(candidate),
                            (Some(best), false) => best.max(candidate),
                            (None, _) => candidate,
                        });
                    }
                    continue;
                }
                stack.push((crate::kernel::eval::canonical_term(other), strict));
            }
        }
        best
    }

    pub(in crate::kernel) fn decide_from_overflow_facts(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        match condition {
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
                if self.decide(&ConditionTerm::equal(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                )) == Some(true)
                {
                    return Some(false);
                }
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                let zero = Bitvector32Term::Constant(0);
                let ordered_nonnegative = self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(right.clone(), zero.clone()),
                    true,
                ) && self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                );
                let nonnegative_minus_one = right == Bitvector32Term::Constant(1)
                    && (self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(left.clone(), zero.clone()),
                        true,
                    ) || self.has_lower_bound_at_or_above(&left, &zero));
                if ordered_nonnegative || nonnegative_minus_one {
                    return Some(false);
                }
                if right == Bitvector32Term::Constant(1) {
                    let int_min = Bitvector32Term::Constant(i32::MIN as u32);
                    let strict_lower_bound = self.condition_facts.iter().find_map(
                        |(condition, value)| {
                            (matches!(
                                (condition, value),
                                (ConditionTerm::Bitvector32SignedLessThan(lower, fact_left), true)
                                    if lower.as_ref() == &int_min
                                        && fact_left.as_ref() == &left
                            ) || matches!(
                                (condition, value),
                                (ConditionTerm::Bitvector32SignedGreaterThan(fact_left, lower), true)
                                    if lower.as_ref() == &int_min
                                        && fact_left.as_ref() == &left
                            ))
                            .then(|| Proposition::ConditionIs(condition.clone(), *value))
                        },
                    );
                    if let Some(provenance) = &strict_lower_bound {
                        record_implicit_reasoning_provenance(self, provenance);
                        return Some(false);
                    }
                }
                // The operands' intervals subtracted over the integers: the
                // subtraction is defined exactly when that fits. Not the
                // `signed_interval` of the difference, which reads the bounds
                // recorded on the difference itself first; those bound its
                // wrapped value, and a wrapped difference of `5` (from
                // `INT_MIN - (INT_MAX - 4)`) says nothing about overflow.
                //
                // Each operand's range is first moved past the values exact
                // disequalities on it exclude. Unary minus lowers to `0 - x`,
                // which overflows at exactly one value of `x`, so the one
                // fact `x != INT_MIN` decides it: `x` then ranges over
                // `[INT_MIN + 1, INT_MAX]` and the difference fits. Each
                // exclusion step is one keyed disequality lookup on the
                // operand, never a scan.
                let (left_lower, left_upper) = self.signed_interval_past_exclusions(&left)?;
                let (right_lower, right_upper) = self.signed_interval_past_exclusions(&right)?;
                let lower = i128::from(left_lower) - i128::from(right_upper);
                let upper = i128::from(left_upper) - i128::from(right_lower);
                (i128::from(i32::MIN) <= lower && upper <= i128::from(i32::MAX)).then_some(false)
            }
            ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                // An established definedness fact follows the same typed
                // operand classes as other checked predicates. No interval
                // reconstruction is needed to reuse that evidence.
                let reversed = ConditionTerm::signed_add_overflows(
                    right.as_ref().clone(),
                    left.as_ref().clone(),
                );
                for value in [false, true] {
                    if self.equality_graph.knows_condition(condition, value)
                        || self.equality_graph.knows_condition(&reversed, value)
                    {
                        return Some(value);
                    }
                }

                if right.as_ref() == &Bitvector32Term::Constant(1) {
                    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
                    let left = left.as_ref().clone();
                    // Keep the direct increment certificate ahead of general
                    // interval reconstruction. Loop execution commonly has
                    // an exact strict bound on a materialized local even when
                    // that bound is awkward to transport into a full range.
                    let strict_upper_bound =
                        self.condition_facts.iter().find_map(|(condition, value)| {
                            match (condition, value) {
                                (ConditionTerm::Bitvector32SignedLessThan(fact_left, _), true) => {
                                    (fact_left.as_ref() == &left).then(|| {
                                        Proposition::ConditionIs(condition.clone(), *value)
                                    })
                                }
                                (
                                    ConditionTerm::Bitvector32SignedGreaterThan(_, fact_left),
                                    true,
                                ) => (fact_left.as_ref() == &left)
                                    .then(|| Proposition::ConditionIs(condition.clone(), *value)),
                                _ => None,
                            }
                        });
                    let direct_nonoverflowing_upper_bound =
                        self.condition_facts.iter().find_map(|(condition, value)| {
                            matches!(
                                (condition, value),
                                (ConditionTerm::Bitvector32SignedLessEqual(fact_left, upper), true)
                                    if fact_left.as_ref() == &left
                                        && signed_bitvector_constant(upper)
                                            .is_some_and(|upper| upper < i64::from(i32::MAX))
                            )
                            .then(|| Proposition::ConditionIs(condition.clone(), *value))
                        });
                    if let Some(provenance) = strict_upper_bound
                        .as_ref()
                        .or(direct_nonoverflowing_upper_bound.as_ref())
                    {
                        record_implicit_reasoning_provenance(self, provenance);
                    }
                    let direct_nonoverflow = strict_upper_bound.is_some()
                        || direct_nonoverflowing_upper_bound.is_some()
                        || self.has_condition_fact(
                            ConditionTerm::signed_less_than(left.clone(), int_max.clone()),
                            true,
                        )
                        || self.has_upper_bound_below(&left, &int_max);
                    if direct_nonoverflow {
                        return Some(false);
                    }
                    // A materialized local may carry an expression such as
                    // `(x + 1)` rather than a direct order fact. Reconstruct
                    // its conservative interval before giving up on the fast
                    // increment rule; nested additions are admitted only when
                    // each inner range itself stays within int32.
                    return self.signed_addition_interval_nonoverflow(
                        &left,
                        &Bitvector32Term::Constant(1),
                    );
                }
                self.signed_addition_interval_nonoverflow(left, right)
            }
            ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
                // An unbounded int64 still has its full-width value range.
                // This discharges x + zero (including a returned zero) without
                // inventing tighter bounds or assuming the inner operations fit.
                crate::kernel::primitives::int64_add_interval_fits(
                    Some(self.int64_interval(left).unwrap_or((i64::MIN, i64::MAX))),
                    Some(self.int64_interval(right).unwrap_or((i64::MIN, i64::MAX))),
                )
                .then_some(false)
            }
            ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
                if self.decide(&ConditionTerm::int64_equal(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                )) == Some(true)
                {
                    return Some(false);
                }
                crate::kernel::primitives::int64_subtract_interval_fits(
                    Some(self.int64_interval(left).unwrap_or((i64::MIN, i64::MAX))),
                    Some(self.int64_interval(right).unwrap_or((i64::MIN, i64::MAX))),
                )
                .then_some(false)
            }
            ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
                let (a, b) = self.int64_interval(left).unwrap_or((i64::MIN, i64::MAX));
                let (c, d) = self.int64_interval(right).unwrap_or((i64::MIN, i64::MAX));
                let products = [
                    i128::from(a) * i128::from(c),
                    i128::from(a) * i128::from(d),
                    i128::from(b) * i128::from(c),
                    i128::from(b) * i128::from(d),
                ];
                products
                    .iter()
                    .all(|value| *value >= i128::from(i64::MIN) && *value <= i128::from(i64::MAX))
                    .then_some(false)
            }
            ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
                let (a, _) = self.int64_interval(left).unwrap_or((i64::MIN, i64::MAX));
                let (c, d) = self.int64_interval(right).unwrap_or((i64::MIN, i64::MAX));
                // This guard includes zero and the sole signed overflow pair MIN / -1.
                ((c > 0 || d < 0) && (a > i64::MIN || c > -1 || d < -1)).then_some(false)
            }
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
                if right.as_ref() == &Bitvector32Term::Constant(0)
                    || left.as_ref() == &Bitvector32Term::Constant(0)
                    || right.as_ref() == &Bitvector32Term::Constant(1)
                    || left.as_ref() == &Bitvector32Term::Constant(1) =>
            {
                Some(false)
            }
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
                if right.as_ref() == &Bitvector32Term::Constant((-1i32) as u32) =>
            {
                let int_min = Bitvector32Term::Constant(i32::MIN as u32);
                let left = left.as_ref().clone();
                self.decide(&ConditionTerm::equal(left, int_min))
            }
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
                if left.as_ref() == &Bitvector32Term::Constant((-1i32) as u32) =>
            {
                let int_min = Bitvector32Term::Constant(i32::MIN as u32);
                let right = right.as_ref().clone();
                self.decide(&ConditionTerm::equal(right, int_min))
            }
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
                self.signed_multiplication_interval_nonoverflow(left, right)
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
                if right.as_ref() == &Bitvector32Term::Constant((-1i32) as u32) =>
            {
                let int_min = Bitvector32Term::Constant(i32::MIN as u32);
                let left = left.as_ref().clone();
                self.decide(&ConditionTerm::equal(left, int_min))
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
                if left.as_ref() == &Bitvector32Term::Constant(i32::MIN as u32) =>
            {
                let minus_one = Bitvector32Term::Constant((-1i32) as u32);
                let right = right.as_ref().clone();
                self.decide(&ConditionTerm::equal(right, minus_one))
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(_, right) if matches!(right.as_ref(), Bitvector32Term::Constant(value) if *value != (-1i32) as u32) => {
                Some(false)
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(left, _) if matches!(left.as_ref(), Bitvector32Term::Constant(value) if *value != i32::MIN as u32) => {
                Some(false)
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
                // Both operands are symbolic here; the arms above decide every
                // constant operand. The zero divisor is split off before this
                // condition is asked (`apply_c_int32_division_nonzero`), and the
                // condition is exactly `left == INT_MIN && right == -1`
                // (`ConditionTerm::signed_divide_overflows`), so, as the int64
                // arm decides from intervals, a divisor range without `-1` or
                // a dividend range without `INT_MIN` says the division does
                // not overflow. The ranges are each operand's own, moved past
                // the values its exact disequalities exclude, and a recorded
                // `right != -1` or `left != INT_MIN` is then read directly:
                // `-1` lies inside a divisor range and no endpoint walk reaches
                // it. Every read is keyed on the operand asked about.
                let int_min = i64::from(i32::MIN);
                let full_range = (int_min, i64::from(i32::MAX));
                let (dividend_lower, dividend_upper) = self
                    .signed_interval_past_exclusions(left)
                    .unwrap_or(full_range);
                let (divisor_lower, divisor_upper) = self
                    .signed_interval_past_exclusions(right)
                    .unwrap_or(full_range);
                if dividend_lower > int_min || divisor_lower > -1 || divisor_upper < -1 {
                    return Some(false);
                }
                if dividend_lower == dividend_upper && divisor_lower == divisor_upper {
                    // Both operands are the one overflowing pair.
                    return Some(true);
                }
                let dividend_excluded = self.has_condition_fact(
                    ConditionTerm::equal(
                        left.as_ref().clone(),
                        Bitvector32Term::Constant(i32::MIN as u32),
                    ),
                    false,
                );
                let divisor_excluded = self.has_condition_fact(
                    ConditionTerm::equal(
                        right.as_ref().clone(),
                        Bitvector32Term::Constant((-1i32) as u32),
                    ),
                    false,
                );
                (dividend_excluded
                    || divisor_excluded
                    || self.divide_overflow_excluded_by_disjunction(left, right))
                .then_some(false)
            }
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, _)
                if left.as_ref() == &Bitvector32Term::Constant(0) =>
            {
                Some(false)
            }
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, right)
                if right.as_ref() == &Bitvector32Term::Constant(0) =>
            {
                Some(false)
            }
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
                let count = right.as_ref().as_const()? as i32;
                if !(0..32).contains(&count) {
                    return None;
                }

                let left = left.as_ref().clone();
                let zero = Bitvector32Term::Constant(0);
                let max_safe_left = Bitvector32Term::Constant((i32::MAX >> count) as u32);
                ((self.decide(&ConditionTerm::signed_greater_equal(
                    left.clone(),
                    zero.clone(),
                )) == Some(true)
                    || self.has_lower_bound_at_or_above(&left, &zero))
                    && (self.decide(&ConditionTerm::signed_less_equal(
                        left.clone(),
                        max_safe_left.clone(),
                    )) == Some(true)
                        || self.has_upper_bound_at_or_below(&left, &max_safe_left)))
                .then_some(false)
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                if left.as_ref().is_subtract_one()
                    && right.as_ref() == &Bitvector32Term::Constant(0) =>
            {
                let left_before_sub = left.as_ref().subtract_one_base()?;
                let zero = Bitvector32Term::Constant(0);
                (self.has_condition_fact(
                    ConditionTerm::signed_greater_than(left_before_sub.clone(), zero.clone()),
                    true,
                ) || self.has_lower_bound_above(&left_before_sub, &zero))
                .then_some(true)
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
                if left.as_ref() == &Bitvector32Term::Constant(0)
                    && right.as_ref().is_subtract_one() =>
            {
                let right_before_sub = right.as_ref().subtract_one_base()?;
                let zero = Bitvector32Term::Constant(0);
                (self.has_condition_fact(
                    ConditionTerm::signed_greater_than(right_before_sub.clone(), zero.clone()),
                    true,
                ) || self.has_lower_bound_above(&right_before_sub, &zero))
                .then_some(true)
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right)
                if left.as_ref().subtract_one_base().is_some_and(|base| {
                    &base == right.as_ref()
                        && (self.has_condition_fact(
                            ConditionTerm::signed_greater_than(
                                base.clone(),
                                Bitvector32Term::Constant(0),
                            ),
                            true,
                        ) || self.has_lower_bound_above(&base, &Bitvector32Term::Constant(0)))
                }) =>
            {
                Some(true)
            }
            _ => None,
        }
    }

    /// Whether an exact disjunction fact excludes the one operand pair at
    /// which `left / right` overflows: `left != INT_MIN or right != -1`, in
    /// either arm order, as `requires` and `have` record it (each arm a
    /// disequality, the disjunction kept whole as a proposition fact). Two
    /// keyed lookups in the proposition-fact set; no case split and no scan.
    fn divide_overflow_excluded_by_disjunction(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let dividend_differs = Proposition::ConditionIs(
            ConditionTerm::equal(left.clone(), Bitvector32Term::Constant(i32::MIN as u32)),
            false,
        );
        let divisor_differs = Proposition::ConditionIs(
            ConditionTerm::equal(right.clone(), Bitvector32Term::Constant((-1i32) as u32)),
            false,
        );
        crate::instrumentation::record_deterministic_work(2);
        self.contains_proposition_fact(&Proposition::Or(
            Box::new(dividend_differs.clone()),
            Box::new(divisor_differs.clone()),
        )) || self.contains_proposition_fact(&Proposition::Or(
            Box::new(divisor_differs),
            Box::new(dividend_differs),
        ))
    }

    pub(in crate::kernel) fn exact_signed_intervals_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        let (left_lower, left_upper) = self.signed_interval(left)?;
        let (right_lower, right_upper) = self.signed_interval(right)?;
        (left_lower == left_upper && right_lower == right_upper)
            .then_some(left_lower == right_lower)
    }

    fn signed_addition_interval_nonoverflow(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        self.signed_interval(left)
            .zip(self.signed_interval(right))
            .and_then(|((left_lower, left_upper), (right_lower, right_upper))| {
                let lower = left_lower.checked_add(right_lower)?;
                let upper = left_upper.checked_add(right_upper)?;
                (lower >= i64::from(i32::MIN) && upper <= i64::from(i32::MAX)).then_some(false)
            })
    }

    /// The range of an `int64` term: its width range from the root
    /// constructor, narrowed by the constant `int64` order bounds indexed
    /// under the term or its canonical alias. These are keyed lookups on the
    /// queried term only, never a scan of the context. A term with neither a
    /// width range nor an indexed bound on both sides has no interval.
    pub(super) fn decide_indexed_greater_equal(&self, condition: &ConditionTerm) -> Option<bool> {
        let ConditionTerm::Bitvector32SignedGreaterEqual(left, right) = condition else {
            return None;
        };
        let right = right.as_const()? as i32 as i64;
        let (lower, upper) = self.indexed_constant_interval(left)?;
        if upper < right {
            Some(false)
        } else if lower >= right {
            Some(true)
        } else {
            None
        }
    }

    // A clear-sign-bit mask has a local range. Keep comparison terms intact
    // so arithmetic certificates retain their original proposition shapes.
    pub(super) fn decide_masked_order(&self, condition: &ConditionTerm) -> Option<bool> {
        fn range(term: &Bitvector32Term) -> Option<(i64, i64)> {
            if let Some(value) = term.as_const() {
                let value = value as i32 as i64;
                return Some((value, value));
            }
            let Bitvector32Term::BitwiseAnd(a, b) = term else {
                return None;
            };
            let mask = a.as_const().or_else(|| b.as_const())?;
            (mask <= i32::MAX as u32).then_some((0, mask as i64))
        }
        let (left, right, strict) = match condition {
            ConditionTerm::Bitvector32SignedLessThan(a, b) => (a, b, true),
            ConditionTerm::Bitvector32SignedLessEqual(a, b) => (a, b, false),
            ConditionTerm::Bitvector32SignedGreaterThan(a, b) => (b, a, true),
            ConditionTerm::Bitvector32SignedGreaterEqual(a, b) => (b, a, false),
            _ => return None,
        };
        let ((llo, lhi), (rlo, rhi)) = (range(left)?, range(right)?);
        if if strict { lhi < rlo } else { lhi <= rlo } {
            Some(true)
        } else if if strict { llo >= rhi } else { llo > rhi } {
            Some(false)
        } else {
            None
        }
    }

    // Bounds through zero extension preserve unsigned order, including the
    // upper half of u32. Read only the queried operand's indexed bounds.
    fn widened_unsigned_interval(&self, term: &Bitvector32Term) -> (i64, i64) {
        if let Some(value) = term.as_const() {
            return (value as i64, value as i64);
        }
        let mut range = (0, u32::MAX as i64);
        let biased =
            Bitvector32Term::bitwise_xor(term.clone(), Bitvector32Term::Constant(0x8000_0000));
        if let Some((lo, hi)) = self.indexed_constant_interval(&biased) {
            range.0 = range.0.max(lo + 0x8000_0000);
            range.1 = range.1.min(hi + 0x8000_0000);
        }
        if let Some((lo, hi)) = self.indexed_constant_interval(term)
            && (lo >= 0 || range.1 <= i32::MAX as i64)
        {
            range.0 = range.0.max(lo);
            range.1 = range.1.min(hi);
        }
        range
    }

    fn widened_unsigned_operand(term: &Bitvector32Term) -> Option<Option<&Bitvector32Term>> {
        match term {
            Bitvector32Term::Int64FromUInt32(value) => Some(Some(value)),
            Bitvector32Term::Int64Constant(value) if (0..=u32::MAX as i64).contains(value) => {
                Some(None)
            }
            _ => None,
        }
    }

    pub(crate) fn widened_unsigned_sum_bound_premises(
        &self,
        condition: &ConditionTerm,
    ) -> Option<Vec<Proposition>> {
        let ConditionTerm::Bitvector64SignedLessEqual(left, _) = condition else {
            return None;
        };
        let Bitvector32Term::Int64Add(a, b) = left.as_ref() else {
            return None;
        };
        let a_operand = Self::widened_unsigned_operand(a)?;
        let b_operand = Self::widened_unsigned_operand(b)?;
        let mut premises = Vec::new();
        for operand in [a_operand, b_operand].into_iter().flatten() {
            let biased = crate::kernel::eval::canonical_term(&Bitvector32Term::bitwise_xor(
                operand.clone(),
                Bitvector32Term::Constant(0x8000_0000),
            ));
            let unsigned = self.signed_constant_bound_facts(SignedDefinedWidth::Int32, &biased);
            let signed = self.signed_constant_bound_facts(
                SignedDefinedWidth::Int32,
                &crate::kernel::eval::canonical_term(operand),
            );
            if unsigned.is_empty() {
                premises.extend(signed);
            } else {
                let unsigned_upper = self
                    .indexed_constant_interval(&biased)
                    .map_or(u32::MAX as i64, |(_, upper)| upper + 0x8000_0000);
                premises.extend(unsigned);
                premises.extend(signed.into_iter().filter(|premise| {
                    if unsigned_upper > i32::MAX as i64 {
                        return true;
                    }
                    let Proposition::ConditionIs(condition, value) = premise else {
                        return false;
                    };
                    condition_as_order_fact(condition, *value).is_some_and(
                        |(lower, upper, strict)| {
                            crate::kernel::eval::canonical_term(&lower)
                                == crate::kernel::eval::canonical_term(operand)
                                && signed_bitvector_constant(&upper)
                                    .is_some_and(|bound| bound - i64::from(strict) < unsigned_upper)
                        },
                    )
                }));
            }
        }
        Some(premises)
    }

    pub(crate) fn decide_widened_sum_bound(&self, condition: &ConditionTerm) -> Option<bool> {
        let ConditionTerm::Bitvector64SignedLessEqual(left, right) = condition else {
            return None;
        };
        let Bitvector32Term::Int64Add(a, b) = left.as_ref() else {
            return None;
        };
        let a_operand = Self::widened_unsigned_operand(a)?;
        let b_operand = Self::widened_unsigned_operand(b)?;
        let bound = right.int64_as_const()?;
        let interval = |term: &Bitvector32Term, operand: Option<&Bitvector32Term>| {
            if let Some(operand) = operand {
                self.widened_unsigned_interval(operand)
            } else {
                let value = term.int64_as_const().expect("checked widened constant");
                (value, value)
            }
        };
        let (a_lo, a_hi) = interval(a, a_operand);
        let (b_lo, b_hi) = interval(b, b_operand);
        if a_hi + b_hi <= bound {
            Some(true)
        } else if a_lo + b_lo > bound {
            Some(false)
        } else {
            None
        }
    }

    pub(super) fn int64_interval(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
        if let Some(bits) = self.wide_constant_from_equalities(term) {
            let value = bits as i64;
            return Some((value, value));
        }
        let (mut lower, mut upper) = term.int64_width_interval().unwrap_or((i64::MIN, i64::MAX));
        let canonical = crate::kernel::eval::canonical_term(term);
        let keys = if canonical == *term {
            vec![term]
        } else {
            vec![term, &canonical]
        };
        for key in keys {
            let Some(bounds) = self.int64_signed_order_bounds.get(key) else {
                continue;
            };
            for (_, other, strict, is_upper) in bounds.keys() {
                let Some(value) = other.int64_as_const() else {
                    continue;
                };
                if *is_upper {
                    // `term < value` or `term <= value`.
                    let Some(value) = (if *strict {
                        value.checked_sub(1)
                    } else {
                        Some(value)
                    }) else {
                        continue;
                    };
                    upper = upper.min(value);
                } else {
                    // `value < term` or `value <= term`.
                    let Some(value) = (if *strict {
                        value.checked_add(1)
                    } else {
                        Some(value)
                    }) else {
                        continue;
                    };
                    lower = lower.max(value);
                }
            }
        }
        (lower <= upper && (lower != i64::MIN || upper != i64::MAX)).then_some((lower, upper))
    }

    /// The exact facts that bound the `width` term `term` by a constant: the
    /// order facts of that width indexed under `term` itself and its
    /// recorded constant equalities, each returned as the condition fact the
    /// context holds so a certificate can cite it. These are keyed lookups on
    /// `term` only; each indexed bound costs a bounded number of exact fact
    /// lookups. `int32` and `int64` share this selection and differ only in
    /// the order index read and the comparison constructors.
    pub(crate) fn signed_constant_bound_facts(
        &self,
        width: SignedDefinedWidth,
        term: &Bitvector32Term,
    ) -> Vec<Proposition> {
        use crate::kernel::proof::arithmetic_special::signed_width_constant;
        let mut facts = Vec::new();
        let index = match width {
            SignedDefinedWidth::Int32 => &self.signed_order_bounds,
            SignedDefinedWidth::Int64 => &self.int64_signed_order_bounds,
        };
        if let Some(bounds) = index.get(term) {
            for (endpoint, other, strict, is_upper) in bounds.keys() {
                crate::instrumentation::record_deterministic_work(1);
                if endpoint != term || signed_width_constant(width, other).is_none() {
                    continue;
                }
                let (lower, upper) = if *is_upper {
                    (endpoint.clone(), other.clone())
                } else {
                    (other.clone(), endpoint.clone())
                };
                let order = |operator: SignedOrder, reversed: bool| {
                    let (left, right) = if reversed {
                        (upper.clone(), lower.clone())
                    } else {
                        (lower.clone(), upper.clone())
                    };
                    signed_order_condition(width, operator, left, right)
                };
                let forms = if *strict {
                    [
                        (order(SignedOrder::LessThan, false), true),
                        (order(SignedOrder::GreaterThan, true), true),
                        (order(SignedOrder::LessEqual, true), false),
                        (order(SignedOrder::GreaterEqual, false), false),
                    ]
                } else {
                    [
                        (order(SignedOrder::LessEqual, false), true),
                        (order(SignedOrder::GreaterEqual, true), true),
                        (order(SignedOrder::LessThan, true), false),
                        (order(SignedOrder::GreaterThan, false), false),
                    ]
                };
                if let Some((condition, value)) = forms
                    .into_iter()
                    .find(|(condition, value)| self.condition_facts.get(condition) == Some(value))
                {
                    facts.push(Proposition::ConditionIs(condition, value));
                }
            }
        }
        if let Some(equalities) = self.exact_constant_equalities.get(term) {
            crate::instrumentation::record_deterministic_work(equalities.len().max(1));
            for condition in equalities.keys() {
                let sides = match (width, condition) {
                    (SignedDefinedWidth::Int32, ConditionTerm::Bitvector32Equal(left, right))
                    | (SignedDefinedWidth::Int64, ConditionTerm::Bitvector64Equal(left, right)) => {
                        Some((left, right))
                    }
                    _ => None,
                };
                if let Some((left, right)) = sides
                    && (left.as_ref() == term && signed_width_constant(width, right).is_some()
                        || right.as_ref() == term && signed_width_constant(width, left).is_some())
                {
                    facts.push(Proposition::ConditionIs(condition.clone(), true));
                }
            }
        }
        facts
    }

    fn signed_multiplication_interval_nonoverflow(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        // From the operands, as for subtraction: a bound recorded on the
        // product bounds its wrapped value, not the integer product.
        self.signed_interval_from_operands(&Bitvector32Term::Multiply(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ))
        .map(|_| false)
    }

    /// Decide a signed comparison from the two sides' intervals, when one of
    /// them is a pure conditional.
    ///
    /// The gate is deliberate. A conditional has no order facts of its own --
    /// nothing writes `0 <= if c { 1 } else { 0 }` down -- so the indexed
    /// routes an ordinary comparison uses cannot reach it, while its arms are
    /// written terms whose hull is immediate. An ordinary comparison returns
    /// here before any interval is reconstructed, so this adds no work to the
    /// comparisons that already had an answer.
    pub(super) fn decide_signed_order_from_conditional_interval(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        strict: bool,
    ) -> Option<bool> {
        if !matches!(left, Bitvector32Term::If { .. })
            && !matches!(right, Bitvector32Term::If { .. })
        {
            return None;
        }
        let (left_lower, left_upper) = self.signed_interval(left)?;
        let (right_lower, right_upper) = self.signed_interval(right)?;
        if strict {
            if left_upper < right_lower {
                return Some(true);
            }
            if left_lower >= right_upper {
                return Some(false);
            }
        } else {
            if left_upper <= right_lower {
                return Some(true);
            }
            if left_lower > right_upper {
                return Some(false);
            }
        }
        None
    }

    /// Returns a conservative signed range for `term`'s 32-bit value. Unknown
    /// endpoints use the full int32 range, so callers can still prove
    /// identities such as `x + 0`. A compound term with no recorded bounds of
    /// its own is ranged from its operands only when that evaluation is known
    /// not to overflow ([`Self::signed_interval_from_operands`]); this makes
    /// nested bounds safe to reuse.
    ///
    /// A range is a range of the *value*, and a bound recorded on a compound
    /// term bounds its wrapped value: `0 <= (a - b) <= 10` holds of the
    /// wrapped difference of `INT_MIN` and `INT_MAX - 4`. So a range here is
    /// never evidence that the term's own operation does not overflow; that
    /// question is [`Self::signed_interval_from_operands`].
    pub(in crate::kernel) fn signed_interval(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
        // A successfully reconstructed interval is a function of the fact set
        // and the term alone. Key by fact-set content and
        // term so a nested arithmetic expression reuses its operands' ranges
        // instead of rescanning every order fact at each tree level.
        let key = ambient_assumptions_memo_id(self).map(|id| (id, term.clone()));
        if let Some(hit) = key
            .as_ref()
            .and_then(|key| SIGNED_INTERVAL_MEMO.with(|memo| memo.borrow().get(key).copied()))
        {
            return Some(hit);
        }
        let result = self.signed_interval_uncached(term);
        if let (Some(key), Some(interval)) = (key, result) {
            SIGNED_INTERVAL_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= SIGNED_INTERVAL_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(key, interval);
            });
        }
        result
    }

    /// [`Self::signed_interval`] with each endpoint moved past the values an
    /// exact fact says `term` is not: `0 <= x <= 3` with `x != 1`, `x != 2`
    /// and `x != 3` is `[0, 0]`. Each step is one indexed lookup that matches
    /// a distinct disequality, so the walk is bounded by those facts.
    pub(in crate::kernel) fn signed_interval_past_exclusions(
        &self,
        term: &Bitvector32Term,
    ) -> Option<(i64, i64)> {
        let (mut lower, mut upper) = self.signed_interval(term)?;
        let excluded = |value: i64| {
            crate::instrumentation::record_deterministic_work(1);
            self.has_condition_fact(
                ConditionTerm::equal(term.clone(), Bitvector32Term::Constant(value as i32 as u32)),
                false,
            )
        };
        while lower < upper && excluded(lower) {
            lower += 1;
        }
        while lower < upper && excluded(upper) {
            upper -= 1;
        }
        Some((lower, upper))
    }

    /// The interval is reconstructed over the term's structure, so the walk
    /// is finite with no depth cut: each arithmetic node ranges its operands.
    fn signed_interval_uncached(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
        if let Some(value) = self.bitvector_constant_from_direct_equalities(term) {
            let value = i64::from(value as i32);
            return Some((value, value));
        }
        let (mut lower, mut upper) = self
            .equality_graph
            .signed_int32_interval(term)
            .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
        if lower != i64::from(i32::MIN) && upper != i64::from(i32::MAX) {
            return Some((lower, upper));
        }
        // Compound terms are common in pointer and loop arithmetic. Their
        // direct fact key is enough for a recorded bound, while deep
        // canonicalization of every unresolved term would turn this interval
        // fallback into a hot-path tree walk. Non-compound atoms still use the
        // canonical alias lookup above.
        let exact_bounds = if matches!(
            term,
            Bitvector32Term::Add(_, _)
                | Bitvector32Term::Subtract(_, _)
                | Bitvector32Term::Multiply(_, _)
        ) {
            self.exact_signed_order_bounds_for_key(term)
        } else {
            self.exact_signed_order_bounds(term)
        };
        // Whether some recorded bound on a side links `term` to another term
        // rather than a constant: only then can an order chain add anything.
        let mut linked_upper = false;
        let mut linked_lower = false;
        if let Some(bounds) = exact_bounds {
            for bound in bounds {
                if signed_bitvector_constant(&bound.other).is_none() {
                    if bound.upper {
                        linked_upper = true;
                    } else {
                        linked_lower = true;
                    }
                }
                let Some(value) = signed_bitvector_constant(&bound.other) else {
                    continue;
                };
                if bound.upper {
                    let Some(value) = (if bound.strict {
                        value.checked_sub(1)
                    } else {
                        Some(value)
                    }) else {
                        continue;
                    };
                    upper = upper.min(value);
                } else {
                    let Some(value) = (if bound.strict {
                        value.checked_add(1)
                    } else {
                        Some(value)
                    }) else {
                        continue;
                    };
                    lower = lower.max(value);
                }
            }
            if lower != i64::from(i32::MIN) && upper != i64::from(i32::MAX) {
                return (lower <= upper).then_some((lower, upper));
            }
        }
        // An atom bounded only through another term (`i <= j` with
        // `j < 1000`) takes the constant its order chain reaches. Compound
        // terms are ranged from their operands below, so only atoms walk, and
        // only on a side a recorded bound links to another term.
        if (linked_upper || linked_lower)
            && !matches!(
                term,
                Bitvector32Term::Add(_, _)
                    | Bitvector32Term::Subtract(_, _)
                    | Bitvector32Term::Multiply(_, _)
                    | Bitvector32Term::If { .. }
            )
        {
            if linked_upper
                && upper == i64::from(i32::MAX)
                && let Some(bound) = self.chained_signed_constant_bound(term, true)
            {
                upper = upper.min(bound);
            }
            if linked_lower
                && lower == i64::from(i32::MIN)
                && let Some(bound) = self.chained_signed_constant_bound(term, false)
            {
                lower = lower.max(bound);
            }
            if lower != i64::from(i32::MIN) && upper != i64::from(i32::MAX) {
                return (lower <= upper).then_some((lower, upper));
            }
        }
        match term {
            Bitvector32Term::Add(_, _)
            | Bitvector32Term::Subtract(_, _)
            | Bitvector32Term::Multiply(_, _) => {
                return self.signed_interval_from_operands(term);
            }
            // A signed byte read is its unsigned byte's two's-complement
            // value: below 0x80 the same number, from 0x80 that number less
            // 256, and otherwise somewhere in the signed byte range.
            term if term.signed_byte_operand().is_some() => {
                let unsigned = term.signed_byte_operand().expect("matched above");
                let (unsigned_lower, unsigned_upper) = self
                    .signed_interval(unsigned)
                    .map(|(lower, upper)| (lower.max(0), upper.min(255)))
                    .unwrap_or((0, 255));
                let (lower, upper) = if unsigned_upper <= 127 {
                    (unsigned_lower, unsigned_upper)
                } else if unsigned_lower >= 128 {
                    (unsigned_lower - 256, unsigned_upper - 256)
                } else {
                    (-128, 127)
                };
                return (lower <= upper).then_some((lower, upper));
            }
            // Any other narrowing conversion: its operand's interval moved
            // into the destination range, or that whole range
            // (`narrowed_casts`), within what the context states of it.
            Bitvector32Term::MachineIntegerCast { .. } => {
                if let Some((cast_lower, cast_upper)) = self.narrowed_cast_interval(term) {
                    let (lower, upper) = (lower.max(cast_lower), upper.min(cast_upper));
                    return (lower <= upper).then_some((lower, upper));
                }
            }
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => {
                // A conditional denotes one of its two arms, so any interval
                // containing both contains it. The condition is not consulted:
                // deciding it is condition reasoning, and the hull is sound
                // whichever way it goes. This is two recursive calls on the
                // written arms, memoized like every other node, not a scan.
                let (then_lower, then_upper) = self.signed_interval(then_term)?;
                let (else_lower, else_upper) = self.signed_interval(else_term)?;
                return Some((then_lower.min(else_lower), then_upper.max(else_upper)));
            }
            _ => {}
        }

        for (condition, value) in self.condition_facts.iter() {
            #[cfg(test)]
            SIGNED_INTERVAL_FALLBACK_FACT_VISITS.with(|visits| visits.set(visits.get() + 1));
            let Some((fact_left, fact_right, strict)) = condition_as_order_fact(condition, *value)
            else {
                continue;
            };
            if self.interval_endpoint_matches(term, &fact_left) {
                if let Some(bound) = signed_bitvector_constant(&fact_right) {
                    let Some(bound) = (if strict {
                        bound.checked_sub(1)
                    } else {
                        Some(bound)
                    }) else {
                        continue;
                    };
                    upper = upper.min(bound);
                } else if strict {
                    // Every signed int32 right endpoint is at most INT_MAX.
                    upper = upper.min(i64::from(i32::MAX) - 1);
                }
            }
            if self.interval_endpoint_matches(term, &fact_right) {
                if let Some(bound) = signed_bitvector_constant(&fact_left) {
                    let Some(bound) = (if strict {
                        bound.checked_add(1)
                    } else {
                        Some(bound)
                    }) else {
                        continue;
                    };
                    lower = lower.max(bound);
                } else if strict {
                    // Every signed int32 left endpoint is at least INT_MIN.
                    lower = lower.max(i64::from(i32::MIN) + 1);
                }
            }
        }
        (lower <= upper).then_some((lower, upper))
    }

    /// The range of a 32-bit addition, subtraction or multiplication computed
    /// over the integers from its operands' ranges, when every value in it is
    /// an int32; `None` for any other term or when the computed range leaves
    /// int32. Where this answers, the operation does not overflow for any
    /// operand values the facts admit, so its wrapped value is the integer
    /// one and lies in the range. Unlike [`Self::signed_interval`], it never
    /// reads bounds recorded on `term` itself, which bound only the wrapped
    /// value, so this is the question an overflow decision asks.
    pub(in crate::kernel) fn signed_interval_from_operands(
        &self,
        term: &Bitvector32Term,
    ) -> Option<(i64, i64)> {
        let (lower, upper) = self.integer_interval_from_operands(term)?;
        (i128::from(i32::MIN) <= lower && upper <= i128::from(i32::MAX))
            .then_some((lower as i64, upper as i64))
    }

    /// The integer range of an addition, subtraction or multiplication of
    /// two int32 operands, from the operands' value ranges, with nothing
    /// wrapped. `None` for any other term or an operand with no range.
    fn integer_interval_from_operands(&self, term: &Bitvector32Term) -> Option<(i128, i128)> {
        let (left, right) = match term {
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right) => (left, right),
            _ => return None,
        };
        let (left_lower, left_upper) = self.signed_interval(left)?;
        let (right_lower, right_upper) = self.signed_interval(right)?;
        let (lower, upper) = match term {
            Bitvector32Term::Add(_, _) => (
                i128::from(left_lower) + i128::from(right_lower),
                i128::from(left_upper) + i128::from(right_upper),
            ),
            Bitvector32Term::Subtract(_, _) => (
                i128::from(left_lower) - i128::from(right_upper),
                i128::from(left_upper) - i128::from(right_lower),
            ),
            _ => {
                let products = [
                    i128::from(left_lower) * i128::from(right_lower),
                    i128::from(left_lower) * i128::from(right_upper),
                    i128::from(left_upper) * i128::from(right_lower),
                    i128::from(left_upper) * i128::from(right_upper),
                ];
                (*products.iter().min()?, *products.iter().max()?)
            }
        };
        Some((lower, upper))
    }

    fn interval_endpoint_matches(
        &self,
        target: &Bitvector32Term,
        endpoint: &Bitvector32Term,
    ) -> bool {
        let resolved_matches = |left: &Bitvector32Term, right: &Bitvector32Term| {
            self.resolve_memory_load_term(left).is_some_and(|resolved| {
                &resolved == right || self.bitvector_terms_snapshot_equivalent(&resolved, right)
            })
        };
        target == endpoint
            || self.bitvector_terms_snapshot_equivalent(target, endpoint)
            || resolved_matches(target, endpoint)
            || resolved_matches(endpoint, target)
    }
}

#[derive(Clone, Copy)]
enum SignedOrder {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

/// The signed comparison `left operator right` of `width`.
fn signed_order_condition(
    width: SignedDefinedWidth,
    operator: SignedOrder,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    let (left, right) = (Box::new(left), Box::new(right));
    match (width, operator) {
        (SignedDefinedWidth::Int32, SignedOrder::LessThan) => {
            ConditionTerm::Bitvector32SignedLessThan(left, right)
        }
        (SignedDefinedWidth::Int32, SignedOrder::LessEqual) => {
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
        }
        (SignedDefinedWidth::Int32, SignedOrder::GreaterThan) => {
            ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        }
        (SignedDefinedWidth::Int32, SignedOrder::GreaterEqual) => {
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        }
        (SignedDefinedWidth::Int64, SignedOrder::LessThan) => {
            ConditionTerm::Bitvector64SignedLessThan(left, right)
        }
        (SignedDefinedWidth::Int64, SignedOrder::LessEqual) => {
            ConditionTerm::Bitvector64SignedLessEqual(left, right)
        }
        (SignedDefinedWidth::Int64, SignedOrder::GreaterThan) => {
            ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        }
        (SignedDefinedWidth::Int64, SignedOrder::GreaterEqual) => {
            ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int32_division_overflow_is_decided_from_operand_intervals_and_disequalities() {
        let x = Bitvector32Term::Variable(Variable(95_201));
        let y = Bitvector32Term::Variable(Variable(95_202));
        let constant = |value: i32| Bitvector32Term::Constant(value as u32);
        let divide = ConditionTerm::signed_divide_overflows(x.clone(), y.clone());
        assert_eq!(PureFactContext::new().decide(&divide), None);
        // `y != 0` alone leaves `INT_MIN / -1` open.
        let nonzero = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(y.clone(), constant(0)), false);
        assert_eq!(nonzero.decide(&divide), None);
        // A divisor range without `-1`, on either side of it.
        let positive = nonzero.clone().assume_condition(
            ConditionTerm::signed_greater_than(y.clone(), constant(0)),
            true,
        );
        assert_eq!(positive.decide(&divide), Some(false));
        let below = PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_than(y.clone(), constant(-1)),
            true,
        );
        assert_eq!(below.decide(&divide), Some(false));
        // A dividend range without `INT_MIN`.
        let nonnegative = nonzero.clone().assume_condition(
            ConditionTerm::signed_greater_equal(x.clone(), constant(0)),
            true,
        );
        assert_eq!(nonnegative.decide(&divide), Some(false));
        // A disequality on either operand's one overflowing value.
        let not_minus_one = nonzero
            .clone()
            .assume_condition(ConditionTerm::equal(y.clone(), constant(-1)), false);
        assert_eq!(not_minus_one.decide(&divide), Some(false));
        let not_int_min = nonzero
            .clone()
            .assume_condition(ConditionTerm::equal(x.clone(), constant(i32::MIN)), false);
        assert_eq!(not_int_min.decide(&divide), Some(false));
        // The exact exclusion as one disjunction, in either arm order.
        let dividend_differs =
            Proposition::ConditionIs(ConditionTerm::equal(x.clone(), constant(i32::MIN)), false);
        let divisor_differs =
            Proposition::ConditionIs(ConditionTerm::equal(y.clone(), constant(-1)), false);
        let either = nonzero.clone().assume_proposition(Proposition::Or(
            Box::new(dividend_differs.clone()),
            Box::new(divisor_differs.clone()),
        ));
        assert_eq!(either.decide(&divide), Some(false));
        let either_reversed = nonzero.clone().assume_proposition(Proposition::Or(
            Box::new(divisor_differs),
            Box::new(dividend_differs),
        ));
        assert_eq!(either_reversed.decide(&divide), Some(false));
        // A bound that keeps `-1`, or a disequality elsewhere, leaves it open.
        let wide = nonzero.clone().assume_condition(
            ConditionTerm::signed_less_equal(y.clone(), constant(5)),
            true,
        );
        assert_eq!(wide.decide(&divide), None);
        let other_value =
            nonzero.assume_condition(ConditionTerm::equal(x.clone(), constant(7)), false);
        assert_eq!(other_value.decide(&divide), None);
        // The overflowing pair itself is never decided defined.
        let exceptional = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(x.clone(), constant(i32::MIN)), true)
            .assume_condition(ConditionTerm::equal(y, constant(-1)), true);
        assert_ne!(exceptional.decide(&divide), Some(false));
    }

    #[test]
    fn int32_negation_overflow_is_excluded_by_a_disequality_at_int_min() {
        let x = Bitvector32Term::Variable(Variable(95_301));
        let constant = |value: i32| Bitvector32Term::Constant(value as u32);
        // Unary minus lowers to `0 - x`.
        let negate = ConditionTerm::signed_subtract_overflows(constant(0), x.clone());
        assert_eq!(PureFactContext::new().decide(&negate), None);
        let excluded = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(x.clone(), constant(i32::MIN)), false);
        assert_eq!(excluded.decide(&negate), Some(false));
        let above = PureFactContext::new().assume_condition(
            ConditionTerm::signed_greater_than(x.clone(), constant(i32::MIN)),
            true,
        );
        assert_eq!(above.decide(&negate), Some(false));
        // Excluding another value leaves `INT_MIN` open.
        let other_value = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(x.clone(), constant(0)), false);
        assert_eq!(other_value.decide(&negate), None);
        // The exclusion moves the operand's range by one, no further.
        assert_eq!(
            excluded.decide(&ConditionTerm::signed_subtract_overflows(
                x.clone(),
                constant(1)
            )),
            Some(false)
        );
        assert_eq!(
            excluded.decide(&ConditionTerm::signed_subtract_overflows(x, constant(2))),
            None
        );
    }

    #[test]
    #[ignore = "nightly: 0.5s in the parallel gate"]
    fn widened_unsigned_sum_bounds_are_sound_and_flat_in_unrelated_facts() {
        let a = Bitvector32Term::Variable(Variable(97001));
        let b = Bitvector32Term::Variable(Variable(97002));
        let sum = Bitvector32Term::int64_add(
            Bitvector32Term::int64_from_uint32(a.clone()),
            Bitvector32Term::int64_from_uint32(b.clone()),
        );
        let goal = ConditionTerm::int64_signed_less_equal(
            sum.clone(),
            Bitvector32Term::Int64Constant(u32::MAX as i64),
        );
        let too_small = ConditionTerm::int64_signed_less_equal(
            sum,
            Bitvector32Term::Int64Constant(u32::MAX as i64 - 1),
        );
        let mut works = Vec::new();
        for size in [8, 32, 128, 512] {
            let mut facts = PureFactContext::new();
            for index in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::unsigned_less_equal(
                        Bitvector32Term::Variable(Variable(98000 + index)),
                        Bitvector32Term::Constant(123),
                    ),
                    true,
                );
            }
            facts = facts
                .assume_condition(
                    ConditionTerm::unsigned_less_equal(
                        a.clone(),
                        Bitvector32Term::Constant(u32::MAX - 255),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_greater_equal(b.clone(), Bitvector32Term::Constant(0)),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(b.clone(), Bitvector32Term::Constant(255)),
                    true,
                );
            let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.decide_widened_sum_bound(&goal)
            });
            assert_eq!(answer, Some(true));
            assert_eq!(facts.decide_widened_sum_bound(&too_small), None);
            let selected = facts.widened_unsigned_sum_bound_premises(&goal).unwrap();
            let selected_context = selected
                .iter()
                .fold(PureFactContext::new(), |context, premise| {
                    context.assume_proposition(premise.clone())
                });
            assert_eq!(selected_context.decide_widened_sum_bound(&goal), Some(true));
            use crate::kernel::proof::arithmetic_special::{
                SpecialArithmeticCertificate, SpecialArithmeticNode,
            };
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::UnsignedSumBound {
                    bounds: (0..selected.len()).collect(),
                    result: Proposition::ConditionIs(goal.clone(), true),
                }],
                conclusion: 0,
            };
            certificate
                .check(&Proposition::ConditionIs(goal.clone(), true), &selected)
                .unwrap();
            let forged = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::UnsignedSumBound {
                    bounds: (0..selected.len()).collect(),
                    result: Proposition::ConditionIs(too_small.clone(), true),
                }],
                conclusion: 0,
            };
            assert!(
                forged
                    .check(
                        &Proposition::ConditionIs(too_small.clone(), true),
                        &selected
                    )
                    .is_err()
            );
            let invalid =
                ConditionTerm::unsigned_greater_equal(b.clone(), Bitvector32Term::Constant(256));
            // The signed byte facts alone do not index the biased operand.
            let facts = facts.assume_condition(
                ConditionTerm::unsigned_less_than(b.clone(), Bitvector32Term::Constant(8)),
                true,
            );
            let (answer, order_work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.decide_indexed_greater_equal(&invalid)
            });
            assert_eq!(answer, Some(false));
            works.push(work + order_work);
        }
        assert!(works.iter().all(|work| *work == works[0]), "{works:?}");
        let unknown = PureFactContext::new();
        assert_eq!(unknown.decide_widened_sum_bound(&goal), None);
    }

    /// The `int32_defined` / `int64_defined` closer selects each operand's
    /// constant bounds by keyed lookup. Its deterministic work must be flat
    /// in the number of unrelated constant-bound facts of either width, and
    /// the selected facts must satisfy the kernel checker.
    #[test]
    fn signed_constant_bound_selection_is_flat_in_unrelated_bounds() {
        use crate::kernel::proof::arithmetic_special::{
            SpecialArithmeticCertificate, SpecialArithmeticNode,
        };
        for width in [SignedDefinedWidth::Int32, SignedDefinedWidth::Int64] {
            let constant = |value: i64| match width {
                SignedDefinedWidth::Int32 => Bitvector32Term::Constant(value as i32 as u32),
                SignedDefinedWidth::Int64 => Bitvector32Term::Int64Constant(value),
            };
            let less = |left, right| match width {
                SignedDefinedWidth::Int32 => ConditionTerm::signed_less_than(left, right),
                SignedDefinedWidth::Int64 => ConditionTerm::int64_signed_less_than(left, right),
            };
            let at_least = |left, right| match width {
                SignedDefinedWidth::Int32 => ConditionTerm::signed_greater_equal(left, right),
                SignedDefinedWidth::Int64 => ConditionTerm::int64_signed_greater_equal(left, right),
            };
            let equal = |left, right| match width {
                SignedDefinedWidth::Int32 => ConditionTerm::equal(left, right),
                SignedDefinedWidth::Int64 => ConditionTerm::int64_equal(left, right),
            };
            let a = Bitvector32Term::Variable(Variable(94_001));
            let b = Bitvector32Term::Variable(Variable(94_002));
            let goal = Proposition::ConditionIs(
                match width {
                    SignedDefinedWidth::Int32 => ConditionTerm::Bitvector32SignedAddOverflows(
                        Box::new(a.clone()),
                        Box::new(b.clone()),
                    ),
                    SignedDefinedWidth::Int64 => ConditionTerm::Bitvector64SignedAddOverflows(
                        Box::new(a.clone()),
                        Box::new(b.clone()),
                    ),
                },
                false,
            );
            let mut works = Vec::new();
            for size in [8_u64, 16, 32, 64] {
                let mut assumptions = PureFactContext::new();
                for index in 0..size {
                    let unrelated = Bitvector32Term::Variable(Variable(95_000 + index));
                    let fact = match index % 3 {
                        0 => less(unrelated, constant(1_000)),
                        1 => at_least(unrelated, constant(-1_000)),
                        _ => equal(unrelated, constant(7)),
                    };
                    assumptions = assumptions.assume_condition(fact, true);
                }
                assumptions = assumptions
                    .assume_condition(less(a.clone(), constant(100)), true)
                    .assume_condition(at_least(a.clone(), constant(-5)), true)
                    .assume_condition(equal(b.clone(), constant(1)), true);
                let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let mut facts = assumptions.signed_constant_bound_facts(width, &a);
                    facts.extend(assumptions.signed_constant_bound_facts(width, &b));
                    facts
                });
                assert_eq!(facts.len(), 3, "{width:?} at {size}: {facts:?}");
                let certificate = SpecialArithmeticCertificate {
                    nodes: vec![SpecialArithmeticNode::SignedDefined {
                        width,
                        bounds: (0..facts.len()).collect(),
                        result: goal.clone(),
                    }],
                    conclusion: 0,
                };
                assert_eq!(certificate.check(&goal, &facts), Ok(()), "{width:?}");
                works.push(work);
            }
            assert!(
                works.iter().all(|work| *work == works[0]),
                "{width:?} bound selection work grew with unrelated bounds: {works:?}"
            );
        }
    }

    #[test]
    fn equal_value_intervals_intersect_and_stay_branch_local() {
        let x = Bitvector32Term::Variable(Variable(190_001));
        let y = Bitvector32Term::Variable(Variable(190_002));
        let parent = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(x.clone(), 0u32.into()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(y.clone(), 10u32.into()),
                true,
            );
        let branch = parent
            .clone()
            .assume_condition(ConditionTerm::equal(x.clone(), y.clone()), true);
        assert_eq!(branch.signed_interval(&x), Some((0, 10)));
        assert_eq!(branch.signed_interval(&y), Some((0, 10)));
        assert_eq!(parent.signed_interval(&x), Some((0, i64::from(i32::MAX))));
        assert_eq!(parent.signed_interval(&y), Some((i64::from(i32::MIN), 10)));
        let withdrawn = branch.assume_condition(ConditionTerm::equal(x.clone(), y.clone()), false);
        assert_eq!(
            withdrawn.signed_interval(&x),
            Some((0, i64::from(i32::MAX)))
        );
        assert_eq!(
            withdrawn.signed_interval(&y),
            Some((i64::from(i32::MIN), 10))
        );
    }

    #[test]
    fn equal_value_intervals_preserve_signed_order_and_width() {
        let x = Bitvector32Term::Variable(Variable(190_011));
        let y = Bitvector32Term::Variable(Variable(190_012));
        for (condition, value, expected) in [
            (
                ConditionTerm::signed_less_than(x.clone(), 10u32.into()),
                true,
                (i64::from(i32::MIN), 9),
            ),
            (
                ConditionTerm::signed_less_than(x.clone(), 10u32.into()),
                false,
                (10, i64::from(i32::MAX)),
            ),
            (
                ConditionTerm::signed_less_equal(x.clone(), 10u32.into()),
                false,
                (11, i64::from(i32::MAX)),
            ),
            (
                ConditionTerm::signed_greater_than(x.clone(), 10u32.into()),
                true,
                (11, i64::from(i32::MAX)),
            ),
            (
                ConditionTerm::signed_greater_equal(x.clone(), 10u32.into()),
                false,
                (i64::from(i32::MIN), 9),
            ),
        ] {
            let facts = PureFactContext::new()
                .assume_condition(condition, value)
                .assume_condition(ConditionTerm::equal(x.clone(), y.clone()), true);
            assert_eq!(facts.signed_interval(&y), Some(expected));
        }
        let wide = PureFactContext::new()
            .assume_condition(
                ConditionTerm::int64_signed_greater_equal(
                    x.clone(),
                    Bitvector32Term::Int64Constant(0),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(
                    x.clone(),
                    Bitvector32Term::Int64Constant(10),
                ),
                true,
            )
            .assume_condition(ConditionTerm::int64_equal(x.clone(), y.clone()), true);
        assert_eq!(
            wide.signed_interval(&y),
            Some((i64::from(i32::MIN), i64::from(i32::MAX)))
        );
    }

    #[test]
    fn equal_value_interval_queries_scale_with_delta_and_skip_unrelated_facts() {
        let mut works = Vec::new();
        for size in [32u64, 64, 128] {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let root = Bitvector32Term::Variable(Variable(200_000 + size * 10));
                let mut facts = PureFactContext::new()
                    .assume_condition(
                        ConditionTerm::signed_greater_equal(root.clone(), 0u32.into()),
                        true,
                    )
                    .assume_condition(
                        ConditionTerm::signed_less_equal(root.clone(), 100u32.into()),
                        true,
                    );
                PureFactContext::reset_signed_interval_fallback_fact_visits();
                for index in 0..size {
                    let alias = Bitvector32Term::Variable(Variable(300_000 + size * 10 + index));
                    let unrelated =
                        Bitvector32Term::Variable(Variable(400_000 + size * 10 + index));
                    facts = facts
                        .assume_condition(
                            ConditionTerm::signed_less_equal(unrelated, 1000u32.into()),
                            true,
                        )
                        .assume_condition(ConditionTerm::equal(root.clone(), alias.clone()), true);
                    assert_eq!(facts.signed_interval(&alias), Some((0, 100)));
                }
                assert_eq!(PureFactContext::signed_interval_fallback_fact_visits(), 0);
            });
            assert!(work < 1000 * size as usize, "size={size}, work={work}");
            works.push(work);
        }
        assert!(
            works[2] < 6 * works[0],
            "interval lookup work grew too fast: {works:?}"
        );
    }

    #[test]
    fn exact_signed_bounds_avoid_context_scan() {
        let x = Bitvector32Term::Variable(Variable(91_001));
        let y = Bitvector32Term::Variable(Variable(91_002));
        let mut assumptions = PureFactContext::new();
        for index in 0..128 {
            let unrelated = Bitvector32Term::Variable(Variable(92_000 + index));
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_less_equal(unrelated, Bitvector32Term::Constant(1_000)),
                true,
            );
        }
        for term in [x.clone(), y.clone()] {
            assumptions = assumptions
                .assume_condition(
                    ConditionTerm::signed_greater_equal(term.clone(), Bitvector32Term::Constant(0)),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(term, Bitvector32Term::Constant(1_000)),
                    true,
                );
        }

        PureFactContext::reset_signed_interval_fallback_fact_visits();
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_add_overflows(x, y)),
            Some(false)
        );
        assert_eq!(PureFactContext::signed_interval_fallback_fact_visits(), 0);
    }

    /// `0 <= i`, `i <= j`, `j < 1000` bounds `i` to `[0, 999]`, so neither
    /// `i + 1` nor `i - 1` overflows; without `j < 1000`, `i + 1` may.
    #[test]
    fn an_order_chain_to_a_constant_bounds_an_increment() {
        let i = Bitvector32Term::Variable(Variable(96_001));
        let j = Bitvector32Term::Variable(Variable(96_002));
        let lower_and_link = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), i.clone()),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_equal(i.clone(), j.clone()), true);
        let bounded = lower_and_link.clone().assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(1000)),
            true,
        );
        let increment =
            ConditionTerm::signed_add_overflows(i.clone(), Bitvector32Term::Constant(1));
        assert_eq!(bounded.decide(&increment), Some(false));
        assert_eq!(bounded.signed_interval(&i), Some((0, 999)));
        assert_eq!(
            bounded.decide(&ConditionTerm::signed_subtract_overflows(
                i.clone(),
                Bitvector32Term::Constant(1)
            )),
            Some(false)
        );
        // `j` unbounded: `i` may be INT32_MAX.
        assert_eq!(lower_and_link.decide(&increment), None);
        // A chain ending at a constant that leaves no room is no bound.
        let at_max = lower_and_link.clone().assume_condition(
            ConditionTerm::signed_less_equal(j.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
            true,
        );
        assert_eq!(at_max.decide(&increment), None);
        // The lower direction: `-5 < k <= i`, `i <= 10` ranges `k - 1`.
        let k = Bitvector32Term::Variable(Variable(96_003));
        let below = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Constant((-5i32) as u32),
                    k.clone(),
                ),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_equal(k.clone(), i.clone()), true)
            .assume_condition(
                ConditionTerm::signed_less_equal(i.clone(), Bitvector32Term::Constant(10)),
                true,
            );
        assert_eq!(below.signed_interval(&k), Some((-4, 10)));
        // A lower chain needs a constant below: `m <= k` alone leaves `m`
        // at INT32_MIN possible.
        let m = Bitvector32Term::Variable(Variable(96_004));
        let unbounded_below =
            below.assume_condition(ConditionTerm::signed_less_equal(m.clone(), k.clone()), true);
        assert_eq!(
            unbounded_below.decide(&ConditionTerm::signed_subtract_overflows(
                m,
                Bitvector32Term::Constant(1)
            )),
            None
        );
    }

    /// The chain walk reads the facts on the chain alone: its work grows
    /// linearly with the chain length and not at all with unrelated order
    /// facts, including unrelated chains.
    #[test]
    fn order_chain_bound_work_is_linear_in_the_chain_and_flat_in_unrelated_facts() {
        let chain_context = |length: u64, unrelated: u64| {
            let mut assumptions = PureFactContext::new();
            for index in 0..unrelated {
                let a = Bitvector32Term::Variable(Variable(97_000 + 2 * index));
                let b = Bitvector32Term::Variable(Variable(97_001 + 2 * index));
                assumptions = assumptions
                    .assume_condition(ConditionTerm::signed_less_equal(a, b.clone()), true)
                    .assume_condition(
                        ConditionTerm::signed_less_than(b, Bitvector32Term::Constant(50)),
                        true,
                    );
            }
            let link = |index: u64| Bitvector32Term::Variable(Variable(98_000 + index));
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), link(0)),
                true,
            );
            for index in 0..length {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_equal(link(index), link(index + 1)),
                    true,
                );
            }
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_less_than(link(length), Bitvector32Term::Constant(1000)),
                true,
            );
            (assumptions, link(0))
        };
        let measure = |length: u64, unrelated: u64| {
            let (assumptions, start) = chain_context(length, unrelated);
            let (bound, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.chained_signed_constant_bound(&start, true)
            });
            assert_eq!(bound, Some(999), "length {length}, unrelated {unrelated}");
            work
        };
        let flat = [0, 16, 64, 256].map(|unrelated| measure(8, unrelated));
        assert!(
            flat.iter().all(|work| *work == flat[0]),
            "chain walk work grew with unrelated facts: {flat:?}"
        );
        let by_length = [4, 8, 16, 32].map(|length| measure(length, 16));
        for pair in by_length.windows(2) {
            // Each link is filed at both endpoints, so doubling the chain at
            // most doubles the entries read, plus a constant.
            assert!(
                pair[1] <= 2 * pair[0] + 4,
                "chain walk work is not linear in the chain: {by_length:?}"
            );
        }
        assert!(by_length[3] > by_length[0], "{by_length:?}");
    }

    #[test]
    fn bounded_nested_increment_uses_reconstructed_interval() {
        let x = Bitvector32Term::Variable(Variable(93_001));
        let once = Bitvector32Term::add(x.clone(), Bitvector32Term::Constant(1));
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(x, Bitvector32Term::Constant(2147483645)),
                true,
            );

        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_add_overflows(
                once,
                Bitvector32Term::Constant(1),
            )),
            Some(false)
        );
    }

    #[test]
    fn compound_add_bounds_are_used_before_reconstruction() {
        let x = Bitvector32Term::Variable(Variable(93_003));
        let compound = Bitvector32Term::add(x, Bitvector32Term::Constant(1));
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(compound.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    compound.clone(),
                    Bitvector32Term::Constant(2147483645),
                ),
                true,
            );

        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_add_overflows(
                compound,
                Bitvector32Term::Constant(2),
            )),
            Some(false)
        );
    }

    #[test]
    fn insufficient_nested_increment_bound_does_not_rule_out_overflow() {
        let x = Bitvector32Term::Variable(Variable(93_002));
        let once = Bitvector32Term::add(x.clone(), Bitvector32Term::Constant(1));
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(x, Bitvector32Term::Constant(2147483646)),
                true,
            );

        assert_ne!(
            assumptions.decide(&ConditionTerm::signed_add_overflows(
                once,
                Bitvector32Term::Constant(1),
            )),
            Some(false)
        );
    }

    #[test]
    fn bounded_multiplication_uses_operand_intervals() {
        let x = Bitvector32Term::Variable(Variable(93_004));
        let y = Bitvector32Term::Variable(Variable(93_005));
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(x, Bitvector32Term::Constant(100)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_greater_equal(y.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(y.clone(), Bitvector32Term::Constant(100)),
                true,
            );

        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_multiply_overflows(
                Bitvector32Term::Variable(Variable(93_004)),
                Bitvector32Term::Variable(Variable(93_005)),
            )),
            Some(false)
        );
    }

    /// Bounds recorded on `a - b` or `a * b` bound the wrapped value of that
    /// term, so they never decide that the operation itself does not
    /// overflow: `INT_MIN - (INT_MAX - 4)` wraps to `5` and `65536 * 65536`
    /// to `0`. The value is still ranged by them. Bounded operands still
    /// decide it (`bounded_multiplication_uses_operand_intervals`).
    #[test]
    fn bounds_on_a_wrapped_result_do_not_rule_out_its_overflow() {
        let a = Bitvector32Term::Variable(Variable(93_010));
        let b = Bitvector32Term::Variable(Variable(93_011));
        for result in [
            Bitvector32Term::Subtract(Box::new(a.clone()), Box::new(b.clone())),
            Bitvector32Term::Multiply(Box::new(a.clone()), Box::new(b.clone())),
        ] {
            let assumptions = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_greater_equal(
                        result.clone(),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(result.clone(), Bitvector32Term::Constant(10)),
                    true,
                );
            let overflows = match &result {
                Bitvector32Term::Subtract(..) => {
                    ConditionTerm::signed_subtract_overflows(a.clone(), b.clone())
                }
                _ => ConditionTerm::signed_multiply_overflows(a.clone(), b.clone()),
            };
            assert_ne!(assumptions.decide(&overflows), Some(false), "{result:?}");
            assert_eq!(assumptions.signed_interval(&result), Some((0, 10)));
        }
    }

    fn indicator(variable: u64) -> Bitvector32Term {
        Bitvector32Term::If {
            condition: Box::new(ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(variable)),
                Bitvector32Term::Constant(0),
            )),
            then_term: Box::new(Bitvector32Term::Constant(1)),
            else_term: Box::new(Bitvector32Term::Constant(0)),
        }
    }

    #[test]
    fn a_conditional_is_ranged_by_the_hull_of_its_arms() {
        let assumptions = PureFactContext::new();
        let indicator = indicator(93_006);

        // Both hull bounds are decided, with the condition left undecided.
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                indicator.clone(),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_equal(
                indicator.clone(),
                Bitvector32Term::Constant(1),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_greater_equal(
                indicator.clone(),
                Bitvector32Term::Constant(0),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_than(
                indicator.clone(),
                Bitvector32Term::Constant(2),
            )),
            Some(true)
        );

        // A bound that only one arm satisfies stays undecided, and one that
        // neither arm satisfies is decided false.
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_equal(
                indicator.clone(),
                Bitvector32Term::Constant(0),
            )),
            None
        );
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_than(
                Bitvector32Term::Constant(1),
                indicator,
            )),
            Some(false)
        );
    }

    #[test]
    fn a_conditional_over_bounded_variables_uses_their_intervals() {
        let x = Bitvector32Term::Variable(Variable(93_007));
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(3)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(x.clone(), Bitvector32Term::Constant(9)),
                true,
            );
        let conditional = Bitvector32Term::If {
            condition: Box::new(ConditionTerm::equal(
                x.clone(),
                Bitvector32Term::Constant(5),
            )),
            then_term: Box::new(x),
            else_term: Box::new(Bitvector32Term::Constant(4)),
        };

        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(3),
                conditional.clone(),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_equal(
                conditional.clone(),
                Bitvector32Term::Constant(9),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_equal(
                conditional,
                Bitvector32Term::Constant(8),
            )),
            None
        );
    }

    #[test]
    fn widened_32_bit_operands_cannot_overflow_int64_addition() {
        let t = Bitvector32Term::int64_from_uint32(Bitvector32Term::Variable(Variable(94_001)));
        let x = Bitvector32Term::int64_from_32(Bitvector32Term::Variable(Variable(94_002)));
        let wide = Bitvector32Term::Variable(Variable(94_003));

        // The widening constructors alone range both operands.
        assert_eq!(
            ConditionTerm::int64_signed_add_overflows(t.clone(), x.clone()),
            ConditionTerm::Constant(false)
        );
        assert_eq!(
            ConditionTerm::int64_signed_subtract_overflows(t.clone(), x.clone()),
            ConditionTerm::Constant(false)
        );
        assert_eq!(
            ConditionTerm::int64_signed_subtract_overflows(x.clone(), t.clone()),
            ConditionTerm::Constant(false)
        );
        // A width range does not fit next to a constant at the int64 edge.
        let max = Bitvector32Term::Int64Constant(i64::MAX);
        assert!(matches!(
            ConditionTerm::int64_signed_add_overflows(t.clone(), max.clone()),
            ConditionTerm::Bitvector64SignedAddOverflows(_, _)
        ));
        assert!(matches!(
            ConditionTerm::int64_signed_add_overflows(x.clone(), max),
            ConditionTerm::Bitvector64SignedAddOverflows(_, _)
        ));
        // An int64 atom has no width range of its own.
        let unbounded = ConditionTerm::int64_signed_add_overflows(wide, t);
        assert!(matches!(
            unbounded,
            ConditionTerm::Bitvector64SignedAddOverflows(_, _)
        ));
        assert_eq!(PureFactContext::new().decide(&unbounded), None);
    }

    #[test]
    fn int64_division_and_multiplication_guards_use_only_queried_bounds() {
        let n = Bitvector32Term::Variable(Variable(95_101));
        let d = Bitvector32Term::Variable(Variable(95_102));
        let constant = Bitvector32Term::Int64Constant;
        let positive = PureFactContext::new().assume_condition(
            ConditionTerm::int64_signed_greater_than(d.clone(), constant(0)),
            true,
        );
        let divide = ConditionTerm::int64_signed_divide_overflows(n.clone(), d.clone());
        assert_eq!(positive.decide(&divide), Some(false));
        assert_eq!(
            positive.decide(&ConditionTerm::int64_equal(d.clone(), constant(0))),
            Some(false)
        );
        assert_eq!(
            Bitvector32Term::int64_subtract(n.clone(), n.clone()),
            constant(0)
        );
        assert_eq!(PureFactContext::new().decide(&divide), None);
        let exact = PureFactContext::new()
            .assume_condition(ConditionTerm::int64_equal(n.clone(), constant(7)), true)
            .assume_condition(ConditionTerm::int64_equal(d.clone(), constant(3)), true);
        assert_eq!(exact.decide(&divide), Some(false));
        let exceptional = PureFactContext::new()
            .assume_condition(
                ConditionTerm::int64_equal(n.clone(), constant(i64::MIN)),
                true,
            )
            .assume_condition(ConditionTerm::int64_equal(d.clone(), constant(-1)), true);
        assert_ne!(exceptional.decide(&divide), Some(false));
        assert_ne!(
            PureFactContext::new()
                .assume_condition(ConditionTerm::int64_equal(d.clone(), constant(0)), true)
                .decide(&divide),
            Some(false)
        );
        let multiply = ConditionTerm::int64_signed_multiply_overflows(constant(2), n.clone());
        let bounded = PureFactContext::new()
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(constant(i64::MIN / 2), n.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(n.clone(), constant(i64::MAX / 2)),
                true,
            );
        assert_eq!(bounded.decide(&multiply), Some(false));
        assert_eq!(PureFactContext::new().decide(&multiply), None);
        let same = ConditionTerm::int64_signed_subtract_overflows(n.clone(), n.clone());
        assert_eq!(PureFactContext::new().decide(&same), Some(false));
    }

    #[test]
    fn int64_guard_work_is_independent_of_unrelated_facts() {
        let n = Bitvector32Term::Variable(Variable(95_111));
        let d = Bitvector32Term::Variable(Variable(95_112));
        let constant = Bitvector32Term::Int64Constant;
        let mut work_counts = Vec::new();
        for size in [8, 32, 128, 512] {
            let mut facts = PureFactContext::new();
            for index in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::int64_signed_less_equal(
                        Bitvector32Term::Variable(Variable(96_000 + index)),
                        constant(123),
                    ),
                    true,
                );
            }
            facts = facts
                .assume_condition(ConditionTerm::int64_equal(n.clone(), constant(7)), true)
                .assume_condition(
                    ConditionTerm::int64_signed_greater_than(d.clone(), constant(0)),
                    true,
                );
            let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
                [
                    facts.decide(&ConditionTerm::int64_signed_divide_overflows(
                        n.clone(),
                        d.clone(),
                    )),
                    facts.decide(&ConditionTerm::int64_signed_multiply_overflows(
                        n.clone(),
                        constant(2),
                    )),
                    facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                        n.clone(),
                        n.clone(),
                    )),
                ]
            });
            assert_eq!(answers, [Some(false); 3]);
            work_counts.push(work);
        }
        assert!(
            work_counts.iter().all(|work| *work == work_counts[0]),
            "{work_counts:?}"
        );
        assert!(work_counts[0] > 0);
    }

    #[test]
    fn int64_constant_division_and_remainder_are_partial_without_panicking() {
        let constant = Bitvector32Term::Int64Constant;
        for (n, d, quotient, remainder) in [
            (7, 3, Some(2), Some(1)),
            (-7, 3, Some(-2), Some(-1)),
            (i64::MIN, -1, None, None),
            (7, 0, None, None),
        ] {
            assert_eq!(
                Bitvector32Term::int64_divide(constant(n), constant(d)).int64_as_const(),
                quotient
            );
            assert_eq!(
                Bitvector32Term::int64_remainder(constant(n), constant(d)).int64_as_const(),
                remainder
            );
        }
    }

    #[test]
    fn int64_order_bounds_decide_addition_and_subtraction_overflow() {
        let a = Bitvector32Term::Variable(Variable(95_001));
        let b = Bitvector32Term::Variable(Variable(95_002));
        let constant = Bitvector32Term::Int64Constant;
        let half = 1i64 << 62;
        let bounded = |a_lower: i64, a_upper: i64, b_lower: i64, b_upper: i64| {
            PureFactContext::new()
                .assume_condition(
                    ConditionTerm::int64_signed_less_equal(constant(a_lower), a.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::int64_signed_less_equal(a.clone(), constant(a_upper)),
                    true,
                )
                .assume_condition(
                    ConditionTerm::int64_signed_less_equal(constant(b_lower), b.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::int64_signed_less_equal(b.clone(), constant(b_upper)),
                    true,
                )
        };
        let add = ConditionTerm::int64_signed_add_overflows(a.clone(), b.clone());
        let subtract = ConditionTerm::int64_signed_subtract_overflows(a.clone(), b.clone());

        assert_eq!(bounded(0, 1000, 0, 1000).decide(&add), Some(false));
        // The exact int64 edge still fits; one past it does not.
        assert_eq!(
            bounded(-half, half - 1, -half, half).decide(&subtract),
            Some(false)
        );
        assert_eq!(bounded(-half, half, -half, half).decide(&subtract), None);
        assert_eq!(bounded(0, half, 0, half).decide(&add), None);
        assert_eq!(bounded(0, half - 1, 0, half).decide(&add), Some(false));

        // Upper bounds alone leave a negative overflow reachable.
        let upper_only = PureFactContext::new()
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(a.clone(), constant(1000)),
                true,
            )
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(b.clone(), constant(1000)),
                true,
            );
        assert_eq!(upper_only.decide(&add), None);

        // A false strict order is the reversed non-strict order: `!(a < 0)`
        // is `0 <= a`, and `!(1000 < a)` is `a <= 1000`.
        let negated = PureFactContext::new()
            .assume_condition(
                ConditionTerm::int64_signed_less_than(a.clone(), constant(0)),
                false,
            )
            .assume_condition(
                ConditionTerm::int64_signed_less_than(constant(1000), a.clone()),
                false,
            )
            .assume_condition(
                ConditionTerm::int64_signed_greater_equal(b.clone(), constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::int64_signed_greater_than(constant(1001), b.clone()),
                true,
            );
        assert_eq!(negated.decide(&add), Some(false));

        // Int32 order facts about the same term never bound it as an int64.
        let int32_bounded = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), a.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(a.clone(), Bitvector32Term::Constant(1000)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), b.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(b.clone(), Bitvector32Term::Constant(1000)),
                true,
            );
        assert_eq!(int32_bounded.decide(&add), None);
    }
    #[test]
    fn int64_zero_alias_addition_and_subtraction_are_safe_and_indexed() {
        let x = Bitvector32Term::Variable(Variable(96_001));
        let zero = Bitvector32Term::Variable(Variable(96_002));
        let constant = Bitvector32Term::Int64Constant;
        let mut baseline_work = None;
        for population in [8u64, 32, 128, 512] {
            let mut facts = PureFactContext::new()
                .assume_condition(ConditionTerm::int64_equal(zero.clone(), constant(0)), true);
            for i in 0..population {
                facts = facts.assume_condition(
                    ConditionTerm::int64_signed_less_equal(
                        Bitvector32Term::Variable(Variable(97_000 + i)),
                        constant(100),
                    ),
                    true,
                );
            }
            let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
                [
                    facts.decide(&ConditionTerm::int64_signed_add_overflows(
                        x.clone(),
                        zero.clone(),
                    )),
                    facts.decide(&ConditionTerm::int64_signed_add_overflows(
                        zero.clone(),
                        x.clone(),
                    )),
                    facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                        x.clone(),
                        zero.clone(),
                    )),
                    facts.decide(&ConditionTerm::int64_equal(
                        Bitvector32Term::int64_add(x.clone(), zero.clone()),
                        x.clone(),
                    )),
                    facts.decide(&ConditionTerm::int64_equal(
                        Bitvector32Term::int64_subtract(x.clone(), zero.clone()),
                        x.clone(),
                    )),
                ]
            });
            assert_eq!(
                answers,
                [
                    Some(false),
                    Some(false),
                    Some(false),
                    Some(true),
                    Some(true)
                ]
            );
            assert!(work > 0);
            assert_eq!(
                facts.decide(&ConditionTerm::int64_equal(
                    Bitvector32Term::int64_add(x.clone(), constant(1)),
                    x.clone()
                )),
                None
            );
            if let Some(baseline) = baseline_work {
                assert_eq!(work, baseline);
            } else {
                baseline_work = Some(work);
            }
            // An unknown nonzero addend/subtrahend can still overflow.
            assert_eq!(
                facts.decide(&ConditionTerm::int64_signed_add_overflows(
                    x.clone(),
                    constant(1)
                )),
                None
            );
            assert_eq!(
                facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                    x.clone(),
                    constant(1)
                )),
                None
            );
            assert_eq!(
                facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                    zero.clone(),
                    x.clone()
                )),
                None
            );
        }
        for edge in [i64::MIN, i64::MAX] {
            let facts = PureFactContext::new()
                .assume_condition(ConditionTerm::int64_equal(zero.clone(), constant(0)), true);
            assert_eq!(
                facts.decide(&ConditionTerm::int64_signed_add_overflows(
                    constant(edge),
                    zero.clone()
                )),
                Some(false)
            );
            assert_eq!(
                facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                    constant(edge),
                    zero.clone()
                )),
                Some(false)
            );
        }
    }
    #[test]
    fn int64_zero_identity_chains_scale_with_the_queried_term() {
        let x = Bitvector32Term::Variable(Variable(98_001));
        let zero = Bitvector32Term::Variable(Variable(98_002));
        let facts = PureFactContext::new().assume_condition(
            ConditionTerm::int64_equal(zero.clone(), Bitvector32Term::Int64Constant(0)),
            true,
        );
        let mut previous = None;
        for depth in [8usize, 32, 128, 512] {
            let mut term = x.clone();
            for _ in 0..depth {
                term = Bitvector32Term::int64_add(term, zero.clone());
            }
            let query = ConditionTerm::int64_equal(term, x.clone());
            let (answer, work) =
                crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
            assert_eq!(answer, Some(true));
            assert!(work > 0);
            if let Some((old_depth, old_work)) = previous {
                assert!(
                    work <= old_work * depth / old_depth + 32,
                    "{depth}: {work}, previous {old_work}"
                );
            }
            previous = Some((depth, work));
        }
    }
    #[test]
    fn bit_preserving_64_bit_conversion_equalities_are_indexed_and_scale() {
        let value = Bitvector32Term::Variable(Variable(99_001));
        let mut baseline = None;
        for population in [8u64, 32, 128, 512] {
            let mut facts = PureFactContext::new();
            for index in 0..population {
                facts = facts.assume_condition(
                    ConditionTerm::uint64_equal(
                        Bitvector32Term::Variable(Variable(100_000 + index)),
                        Bitvector32Term::UInt64Constant(0),
                    ),
                    true,
                );
            }
            let query = ConditionTerm::uint64_equal(
                Bitvector32Term::UInt64FromInt64(Box::new(value.clone())),
                value.clone(),
            );
            let (answer, work) =
                crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
            assert_eq!(answer, Some(true));
            if let Some(previous) = baseline {
                assert_eq!(work, previous);
            } else {
                baseline = Some(work);
            }
        }
        let facts = PureFactContext::new();
        let mut previous = None;
        for depth in [8usize, 32, 128, 512] {
            let mut term = value.clone();
            for _ in 0..depth {
                term = Bitvector32Term::UInt64FromInt64(Box::new(term));
            }
            let query = ConditionTerm::uint64_equal(term, value.clone());
            let (answer, work) =
                crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
            assert_eq!(answer, Some(true));
            if let Some((old_depth, old_work)) = previous {
                assert!(
                    work <= old_work * depth / old_depth + 32,
                    "{depth}: {work}, previous {old_work}"
                );
            }
            previous = Some((depth, work));
        }
    }
}
