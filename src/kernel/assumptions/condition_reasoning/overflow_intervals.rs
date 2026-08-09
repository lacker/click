use super::*;

impl Assumptions {
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
                (ordered_nonnegative || nonnegative_minus_one).then_some(false)
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
                    return (strict_upper_bound.is_some()
                        || direct_nonoverflowing_upper_bound.is_some()
                        || self.has_condition_fact(
                            ConditionTerm::signed_less_than(left.clone(), int_max.clone()),
                            true,
                        )
                        || self.has_upper_bound_below(&left, &int_max))
                    .then_some(false);
                }
                self.signed_interval(left, SIGNED_INTERVAL_DEPTH_LIMIT)
                    .zip(self.signed_interval(right, SIGNED_INTERVAL_DEPTH_LIMIT))
                    .and_then(|((left_lower, left_upper), (right_lower, right_upper))| {
                        let lower = left_lower.checked_add(right_lower)?;
                        let upper = left_upper.checked_add(right_upper)?;
                        (lower >= i64::from(i32::MIN) && upper <= i64::from(i32::MAX))
                            .then_some(false)
                    })
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
        let (left_lower, left_upper) = self.signed_interval(left, SIGNED_INTERVAL_DEPTH_LIMIT)?;
        let (right_lower, right_upper) =
            self.signed_interval(right, SIGNED_INTERVAL_DEPTH_LIMIT)?;
        (left_lower == left_upper && right_lower == right_upper)
            .then_some(left_lower == right_lower)
    }

    /// Returns a conservative signed range for `term`. Unknown endpoints use
    /// the full int32 range, so callers can still prove identities such as
    /// `x + 0`. Additions are ranged only when their own signed evaluation is
    /// known not to overflow; this makes nested-addition bounds safe to reuse.
    fn signed_interval(&self, term: &Bitvector32Term, depth: usize) -> Option<(i64, i64)> {
        if depth == 0 {
            note_search_truncation();
            return None;
        }
        if let Some(value) = self.bitvector_constant_from_direct_equalities(term) {
            let value = i64::from(value as i32);
            return Some((value, value));
        }
        if let Bitvector32Term::Add(left, right) = term {
            let (left_lower, left_upper) = self.signed_interval(left, depth - 1)?;
            let (right_lower, right_upper) = self.signed_interval(right, depth - 1)?;
            let lower = left_lower.checked_add(right_lower)?;
            let upper = left_upper.checked_add(right_upper)?;
            if lower < i64::from(i32::MIN) || upper > i64::from(i32::MAX) {
                return None;
            }
            return Some((lower, upper));
        }

        let mut lower = i64::from(i32::MIN);
        let mut upper = i64::from(i32::MAX);
        for (condition, value) in &self.condition_facts {
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
