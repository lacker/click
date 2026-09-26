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

    pub(in crate::kernel) fn decide_from_overflow_facts(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        match condition {
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
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
                // Reuse the bounded interval reconstruction already used for
                // addition and multiplication, including compound operands.
                self.signed_interval(&Bitvector32Term::Subtract(Box::new(left), Box::new(right)))
                    .map(|_| false)
            }
            ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
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
                crate::kernel::primitives::int64_add_interval_fits(
                    self.int64_interval(left),
                    self.int64_interval(right),
                )
                .then_some(false)
            }
            ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
                crate::kernel::primitives::int64_subtract_interval_fits(
                    self.int64_interval(left),
                    self.int64_interval(right),
                )
                .then_some(false)
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
    fn int64_interval(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
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
        self.signed_interval(&Bitvector32Term::Multiply(
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

    /// Returns a conservative signed range for `term`. Unknown endpoints use
    /// the full int32 range, so callers can still prove identities such as
    /// `x + 0`. Compound arithmetic is ranged only when its own signed
    /// evaluation is known not to overflow; this makes nested bounds safe to
    /// reuse.
    fn signed_interval(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
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

    /// The interval is reconstructed over the term's structure, so the walk
    /// is finite with no depth cut: each arithmetic node ranges its operands.
    fn signed_interval_uncached(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
        if let Some(value) = self.bitvector_constant_from_direct_equalities(term) {
            let value = i64::from(value as i32);
            return Some((value, value));
        }
        let mut lower = i64::from(i32::MIN);
        let mut upper = i64::from(i32::MAX);
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
        if let Some(bounds) = exact_bounds {
            for bound in bounds {
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
        match term {
            Bitvector32Term::Add(left, right) => {
                let (left_lower, left_upper) = self.signed_interval(left)?;
                let (right_lower, right_upper) = self.signed_interval(right)?;
                let lower = left_lower.checked_add(right_lower)?;
                let upper = left_upper.checked_add(right_upper)?;
                if lower < i64::from(i32::MIN) || upper > i64::from(i32::MAX) {
                    return None;
                }
                return Some((lower, upper));
            }
            Bitvector32Term::Subtract(left, right) => {
                let (left_lower, left_upper) = self.signed_interval(left)?;
                let (right_lower, right_upper) = self.signed_interval(right)?;
                let lower = left_lower.checked_sub(right_upper)?;
                let upper = left_upper.checked_sub(right_lower)?;
                if lower < i64::from(i32::MIN) || upper > i64::from(i32::MAX) {
                    return None;
                }
                return Some((lower, upper));
            }
            Bitvector32Term::Multiply(left, right) => {
                let (left_lower, left_upper) = self.signed_interval(left)?;
                let (right_lower, right_upper) = self.signed_interval(right)?;
                let products = [
                    i128::from(left_lower) * i128::from(right_lower),
                    i128::from(left_lower) * i128::from(right_upper),
                    i128::from(left_upper) * i128::from(right_lower),
                    i128::from(left_upper) * i128::from(right_upper),
                ];
                let lower = *products.iter().min()?;
                let upper = *products.iter().max()?;
                if lower < i128::from(i32::MIN) || upper > i128::from(i32::MAX) {
                    return None;
                }
                return Some((lower as i64, upper as i64));
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
    fn an_ordinary_comparison_does_not_reach_the_interval_route() {
        // The route is gated on a conditional, so a comparison between two
        // unbounded variables is still undecided rather than newly ranged.
        let assumptions = PureFactContext::new();
        assert_eq!(
            assumptions.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Variable(Variable(93_008)),
                Bitvector32Term::Variable(Variable(93_009)),
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
}
