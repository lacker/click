use super::*;
use crate::kernel::MachineCastSpelling;
#[cfg(test)]
use crate::kernel::binary_node;
#[cfg(test)]
use crate::kernel::binary_term;
use crate::kernel::int32_constant;
use crate::kernel::{CompareRelation, MachineIntegerType, MachineOperandView, OverflowOperation};
use crate::kernel::{bits32_constant, constant_i64, constant_u32, int64_constant};

#[cfg(test)]
thread_local! {
    static SIGNED_INTERVAL_FALLBACK_FACT_VISITS: Cell<usize> = const { Cell::new(0) };
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

    /// The range of `term` that its own recorded constant order bounds give,
    /// read from the maintained extrema at the term's canonical form: one
    /// keyed lookup, no chain, no scan of its bound bucket. `None` when no
    /// constant bound is filed there. For a caller that runs per cell and
    /// may not search; [`Self::signed_interval`] performs general reconstruction.
    pub(in crate::kernel) fn indexed_constant_interval(
        &self,
        term: &OldMachineTerm,
    ) -> Option<(i64, i64)> {
        self.indexed_constant_interval_view(MachineOperandView::Old(term), false)
    }

    /// Direct unsigned constant extrema, maintained separately from signed facts.
    #[cfg(test)]
    pub(in crate::kernel) fn indexed_unsigned32_constant_interval(
        &self,
        term: &OldMachineTerm,
    ) -> Option<(i64, i64)> {
        self.indexed_constant_interval_view(MachineOperandView::Old(term), true)
    }

    pub(in crate::kernel) fn indexed_constant_interval_view(
        &self,
        term: MachineOperandView<'_>,
        unsigned: bool,
    ) -> Option<(i64, i64)> {
        match term {
            MachineOperandView::Old(term) => {
                let canonical = crate::kernel::eval::canonical_term(term);
                self.checked_order_bounds.interval(&canonical, unsigned)
            }
            // Shared arithmetic contains no atomic load payloads to replace.
            MachineOperandView::Shared(_) => {
                self.checked_order_bounds.interval_view(term, unsigned)
            }
        }
    }

    pub(in crate::kernel) fn indexed_signed_wide_constant_interval_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<(i64, i64)> {
        self.checked_order_bounds.signed_wide_interval_view(term)
    }

    pub(in crate::kernel) fn indexed_unsigned_wide_upper_bound_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<u64> {
        self.checked_order_bounds.unsigned_wide_upper_view(term)
    }

    pub(in crate::kernel) fn decide_from_overflow_facts(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        if let Some(value) = self.exact_condition_value(condition) {
            return Some(value);
        }
        if let Some((format, operation, left, right)) =
            crate::kernel::machine_integer::representation::overflow_operation(condition)
        {
            return self.decide_ring_overflow(
                format,
                operation,
                [
                    MachineOperandView::Old(left),
                    MachineOperandView::Old(right),
                ],
            );
        }
        match condition {
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Divide,
                left,
                right,
            } => {
                let (a, _) = self.int64_interval(left).unwrap_or((i64::MIN, i64::MAX));
                let (c, d) = self.int64_interval(right).unwrap_or((i64::MIN, i64::MAX));
                // This guard includes zero and the sole signed overflow pair MIN / -1.
                ((c > 0 || d < 0) && (a > i64::MIN || c > -1 || d < -1)).then_some(false)
            }
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Divide,
                left,
                right,
            } if right.as_ref() == &OldMachineTerm::constant((-1i32) as u32) => {
                let int_min = OldMachineTerm::constant(i32::MIN as u32);
                let left = left.as_ref().clone();
                self.decide(&OldConditionTerm::equal(left, int_min))
            }
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Divide,
                left,
                right,
            } if left.as_ref() == &OldMachineTerm::constant(i32::MIN as u32) => {
                let minus_one = OldMachineTerm::constant((-1i32) as u32);
                let right = right.as_ref().clone();
                self.decide(&OldConditionTerm::equal(right, minus_one))
            }
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Divide,
                left: _,
                right,
            } if matches!(right.as_ref(), bits32_constant!(value) if constant_u32(*value) != (-1i32) as u32) => {
                Some(false)
            }
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Divide,
                left,
                right: _,
            } if matches!(left.as_ref(), bits32_constant!(value) if constant_u32(*value) != i32::MIN as u32) => {
                Some(false)
            }
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Divide,
                left,
                right,
            } => {
                // Both operands are symbolic here; the arms above decide every
                // constant operand. The zero divisor is split off before this
                // condition is asked (`apply_program_int32_division_nonzero`), and the
                // condition is exactly `left == INT_MIN && right == -1`
                // (`OldConditionTerm::signed_divide_overflows`), so, as the int64
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
                    OldConditionTerm::equal(
                        left.as_ref().clone(),
                        OldMachineTerm::constant(i32::MIN as u32),
                    ),
                    false,
                );
                let divisor_excluded = self.has_condition_fact(
                    OldConditionTerm::equal(
                        right.as_ref().clone(),
                        OldMachineTerm::constant((-1i32) as u32),
                    ),
                    false,
                );
                (dividend_excluded
                    || divisor_excluded
                    || self.divide_overflow_excluded_by_disjunction(left, right))
                .then_some(false)
            }
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::ShiftLeft,
                left,
                right: _,
            } if left.as_ref() == &OldMachineTerm::constant(0) => Some(false),
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::ShiftLeft,
                left: _,
                right,
            } if right.as_ref() == &OldMachineTerm::constant(0) => Some(false),
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::ShiftLeft,
                left,
                right,
            } => {
                let count = right.as_ref().as_const()? as i32;
                if !(0..32).contains(&count) {
                    return None;
                }

                let left = left.as_ref().clone();
                let zero = OldMachineTerm::constant(0);
                let max_safe_left = OldMachineTerm::constant((i32::MAX >> count) as u32);
                ((self.decide(&OldConditionTerm::signed_greater_equal(
                    left.clone(),
                    zero.clone(),
                )) == Some(true)
                    || self.has_lower_bound_at_or_above(&left, &zero))
                    && (self.decide(&OldConditionTerm::signed_less_equal(
                        left.clone(),
                        max_safe_left.clone(),
                    )) == Some(true)
                        || self.has_upper_bound_at_or_below(&left, &max_safe_left)))
                .then_some(false)
            }
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } if left.as_ref().is_subtract_one()
                && right.as_ref() == &OldMachineTerm::constant(0) =>
            {
                let left_before_sub = left.as_ref().subtract_one_base()?;
                let zero = OldMachineTerm::constant(0);
                (self.has_condition_fact(
                    OldConditionTerm::signed_greater_than(left_before_sub.clone(), zero.clone()),
                    true,
                ) || self.has_lower_bound_above(&left_before_sub, &zero))
                .then_some(true)
            }
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } if left.as_ref() == &OldMachineTerm::constant(0)
                && right.as_ref().is_subtract_one() =>
            {
                let right_before_sub = right.as_ref().subtract_one_base()?;
                let zero = OldMachineTerm::constant(0);
                (self.has_condition_fact(
                    OldConditionTerm::signed_greater_than(right_before_sub.clone(), zero.clone()),
                    true,
                ) || self.has_lower_bound_above(&right_before_sub, &zero))
                .then_some(true)
            }
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } if left.as_ref().subtract_one_base().is_some_and(|base| {
                &base == right.as_ref()
                    && (self.has_condition_fact(
                        OldConditionTerm::signed_greater_than(
                            base.clone(),
                            OldMachineTerm::constant(0),
                        ),
                        true,
                    ) || self.has_lower_bound_above(&base, &OldMachineTerm::constant(0)))
            }) =>
            {
                Some(true)
            }
            _ => None,
        }
    }

    /// The original legacy premise for this shared query, selected by its
    /// format, operation, operand identities and polarity.
    pub(in crate::kernel) fn stated_overflow_source(
        &self,
        query: &crate::kernel::machine_integer::definedness::OverflowQueryView,
        truth: bool,
    ) -> Option<&Proposition> {
        self.observation_comparisons.overflow_source(
            query.format,
            query.operation_kind(),
            query
                .operands
                .each_ref()
                .map(|operand| operand.operand_view()),
            truth,
        )
    }

    /// The same membership judgment as `contains_known` on a legacy overflow
    /// predicate, without constructing that predicate. This does not perform
    /// interval reasoning or discharge a new arithmetic obligation.
    pub(in crate::kernel) fn contains_known_overflow_query(
        &self,
        query: &crate::kernel::machine_integer::definedness::OverflowQueryView,
        truth: bool,
    ) -> bool {
        if self.equality_graph.has_scalar_constant_conflict() {
            return true;
        }
        if let Some(source) = self.stated_overflow_source(query, truth) {
            record_implicit_consulted_premises(self, source);
            return true;
        }
        query.format == MachineIntegerType::Int32
            && query.operation == crate::kernel::machine_integer::Operation::Add
            && self.equality_graph.knows_int32_add_overflow_views(
                query
                    .operands
                    .each_ref()
                    .map(|operand| operand.operand_view()),
                truth,
            )
    }

    pub(in crate::kernel) fn knows_operation_range_bound(
        &self,
        bound: &crate::kernel::machine_integer::identity::IntegerOperationRangeBound,
    ) -> bool {
        bound
            .stating_facts()
            .iter()
            .any(|fact| self.contains_known(fact))
            || bound
                .overflow_query()
                .is_some_and(|query| self.contains_known_overflow_query(&query, false))
    }

    /// Ordinary bounds and legacy predicates ask the same arithmetic query.
    /// Only the original operands and their indexed ranges are inspected.
    pub(in crate::kernel) fn decide_overflow_query(
        &self,
        query: &crate::kernel::machine_integer::definedness::OverflowQueryView,
    ) -> Option<bool> {
        let operands = query
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        // Literal and variable roots have fixed-size native spellings. Keep
        // their existing atomic decision route without exporting arithmetic
        // or traversing a shared operand's children.
        let atoms = operands.map(|operand| {
            operand
                .literal()
                .or_else(|| operand.variable().copied().map(OldMachineTerm::Variable))
        });
        let operands = std::array::from_fn(|index| {
            atoms[index]
                .as_ref()
                .map(MachineOperandView::Old)
                .unwrap_or(operands[index])
        });
        if let [
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        ] = operands
        {
            // Legacy producers and atomic roots keep their existing
            // read-over-write and simplification rules.
            let condition = crate::kernel::machine_integer::representation::overflow_condition(
                query.format,
                query.operation,
                Box::new(left.clone()),
                Box::new(right.clone()),
            )?;
            return self.decide_unrecorded(&condition);
        }
        if let Some(value) = self
            .difference_graph
            .built()
            .and_then(|graph| graph.decide_overflow_query(query))
        {
            if let Some(source) = self.stated_overflow_source(query, value) {
                record_implicit_consulted_premises(self, source);
            }
            return Some(value);
        }
        let bounds = query.bounds();
        if bounds.iter().all(|bound| {
            let Proposition::ConditionIs(condition, true) = bound else {
                return false;
            };
            Self::decide_intrinsically(condition.old_form()) == Some(true)
                || integer_order_spellings(condition.old_form())
                    .into_iter()
                    .any(|condition| {
                        self.contains_known(&Proposition::condition_is(condition, true))
                    })
        }) {
            for bound in &bounds {
                record_implicit_consulted_premises(self, bound);
            }
            return Some(false);
        }
        let operation = query.operation_kind();
        for truth in [true, false] {
            if let Some(source) = self.stated_overflow_source(query, truth) {
                record_implicit_consulted_premises(self, source);
                return Some(truth);
            }
        }
        // A retained fold may be an operand of another partial
        // operation. Check its exact value before applying the same domain rules.
        let mut fold_reads = std::collections::HashMap::new();
        let reduced = operands.map(|operand| {
            if !matches!(operand, MachineOperandView::Shared(root) if root.has_machine_folds()) {
                return None;
            }
            crate::kernel::KernelFold::reduce_bounded_int32_in(
                &operand.retain(query.format),
                &mut fold_reads,
            )
        });
        let operands = std::array::from_fn(|index| {
            reduced[index]
                .as_ref()
                .map(MachineOperandView::Shared)
                .unwrap_or(operands[index])
        });
        // The old simplifier folds a query whose operands normalize to
        // constants. Construct only those two literals, never their trees.
        let literal = |operand: MachineOperandView<'_>| {
            operand.literal().or_else(|| match query.format {
                MachineIntegerType::Int32 if operand.variable().is_some() => self
                    .indexed_exact_int32_constant_view(operand)
                    .map(|(value, source)| {
                        record_implicit_consulted_premises(self, &source);
                        OldMachineTerm::constant(value as u32)
                    }),
                MachineIntegerType::Int32 => self
                    .known_signed_constant_after_normalization_view(operand)
                    .map(|value| OldMachineTerm::constant(value as u32)),
                MachineIntegerType::Int64 => self
                    .wide_constant_from_equalities_view(operand)
                    .map(|value| OldMachineTerm::int64_constant(value as i64)),
                _ => None,
            })
        };
        let literals = operands.map(literal);
        if let [Some(left), Some(right)] = &literals
            && let OldConditionTerm::Constant(value) = OldConditionTerm::machine_overflows(
                query.format,
                operation,
                left.clone(),
                right.clone(),
            )
        {
            return Some(value);
        }
        // A single constant alias also matters: for example, the increment
        // certificate recognizes a right operand known to be one.
        let operands = std::array::from_fn(|index| {
            literals[index]
                .as_ref()
                .map(MachineOperandView::Old)
                .unwrap_or(operands[index])
        });
        self.decide_ring_overflow(query.format, query.operation, operands)
    }

    fn decide_ring_overflow(
        &self,
        format: MachineIntegerType,
        operation: crate::kernel::machine_integer::Operation,
        [left, right]: [MachineOperandView<'_>; 2],
    ) -> Option<bool> {
        use crate::kernel::machine_integer::{Operation as Op, Relation as R};
        let zero = OldMachineTerm::constant(0);
        let zero = MachineOperandView::Old(&zero);
        let known = |relation, a, b| self.has_operand_comparison(format, relation, a, b);
        let decide = |relation, a, b| self.decide_operand_comparison(format, relation, a, b);
        match (format, operation) {
            (MachineIntegerType::Int32, Op::Subtract) => {
                if decide(R::Equal, left, right) == Some(true) {
                    return Some(false);
                }
                let right_one = right.literal() == Some(OldMachineTerm::constant(1));
                if (known(R::LessEqual, zero, right) && known(R::LessEqual, right, left))
                    || (right_one
                        && (known(R::LessEqual, zero, left)
                            || self.has_lower_bound_at_or_above_views(left, zero)))
                {
                    return Some(false);
                }
                let minimum = OldMachineTerm::constant(i32::MIN as u32);
                if right_one && known(R::Less, MachineOperandView::Old(&minimum), left) {
                    return Some(false);
                }
                let (a, b) = self.signed_interval_past_exclusions_view(left)?;
                let (c, d) = self.signed_interval_past_exclusions_view(right)?;
                (i128::from(i32::MIN) <= i128::from(a) - i128::from(d)
                    && i128::from(b) - i128::from(c) <= i128::from(i32::MAX))
                .then_some(false)
            }
            (MachineIntegerType::Int32, Op::Add) => {
                for value in [false, true] {
                    if self
                        .equality_graph
                        .knows_int32_add_overflow_views([left, right], value)
                        || self
                            .equality_graph
                            .knows_int32_add_overflow_views([right, left], value)
                    {
                        return Some(value);
                    }
                }
                if right.literal() == Some(OldMachineTerm::constant(1)) {
                    let maximum = OldMachineTerm::constant(i32::MAX as u32);
                    let maximum = MachineOperandView::Old(&maximum);
                    let strict = self.checked_order_bounds.strict_upper_view(left);
                    let direct = self.checked_order_bounds.upper_below_max_view(left);
                    if let Some(source) = strict.as_ref().or(direct.as_ref()) {
                        record_implicit_consulted_premises(self, source);
                    }
                    if strict.is_some()
                        || direct.is_some()
                        || known(R::Less, left, maximum)
                        || self.has_upper_bound_below_views(left, maximum)
                    {
                        return Some(false);
                    }
                }
                let (a, b) = self.signed_interval_view(left)?;
                let (c, d) = self.signed_interval_view(right)?;
                (a.checked_add(c)? >= i64::from(i32::MIN)
                    && b.checked_add(d)? <= i64::from(i32::MAX))
                .then_some(false)
            }
            (MachineIntegerType::Int32, Op::Multiply) => {
                let unit = |operand: MachineOperandView<'_>| {
                    matches!(operand.literal(), Some(int32_constant!(0 | 1)))
                };
                if unit(left) || unit(right) {
                    return Some(false);
                }
                let minus_one = Some(OldMachineTerm::constant((-1i32) as u32));
                let minimum = OldMachineTerm::constant(i32::MIN as u32);
                if right.literal() == minus_one {
                    return decide(R::Equal, left, MachineOperandView::Old(&minimum));
                }
                if left.literal() == minus_one {
                    return decide(R::Equal, right, MachineOperandView::Old(&minimum));
                }
                let (a, b) = self.signed_interval_view(left)?;
                let (c, d) = self.signed_interval_view(right)?;
                [
                    i128::from(a) * i128::from(c),
                    i128::from(a) * i128::from(d),
                    i128::from(b) * i128::from(c),
                    i128::from(b) * i128::from(d),
                ]
                .into_iter()
                .all(|value| i128::from(i32::MIN) <= value && value <= i128::from(i32::MAX))
                .then_some(false)
            }
            (MachineIntegerType::Int64, operation) => {
                if operation == Op::Subtract && decide(R::Equal, left, right) == Some(true) {
                    return Some(false);
                }
                let left = self
                    .int64_interval_view(left)
                    .unwrap_or((i64::MIN, i64::MAX));
                let right = self
                    .int64_interval_view(right)
                    .unwrap_or((i64::MIN, i64::MAX));
                match operation {
                    Op::Add => {
                        crate::kernel::primitives::int64_add_interval_fits(Some(left), Some(right))
                            .then_some(false)
                    }
                    Op::Subtract => crate::kernel::primitives::int64_subtract_interval_fits(
                        Some(left),
                        Some(right),
                    )
                    .then_some(false),
                    Op::Multiply => {
                        let (a, b, c, d) = (
                            i128::from(left.0),
                            i128::from(left.1),
                            i128::from(right.0),
                            i128::from(right.1),
                        );
                        [a * c, a * d, b * c, b * d]
                            .into_iter()
                            .all(|value| {
                                i128::from(i64::MIN) <= value && value <= i128::from(i64::MAX)
                            })
                            .then_some(false)
                    }
                }
            }
            _ => None,
        }
    }

    /// Whether an exact disjunction fact excludes the one operand pair at
    /// which `left / right` overflows: `left != INT_MIN or right != -1`, in
    /// either arm order, as `requires` and `have` record it (each arm a
    /// disequality, the disjunction kept whole as a proposition fact). Two
    /// keyed lookups in the proposition-fact set; no case split and no scan.
    pub(in crate::kernel) fn divide_overflow_excluded_by_disjunction(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> bool {
        let dividend_differs = Proposition::condition_is(
            OldConditionTerm::equal(left.clone(), OldMachineTerm::constant(i32::MIN as u32)),
            false,
        );
        let divisor_differs = Proposition::condition_is(
            OldConditionTerm::equal(right.clone(), OldMachineTerm::constant((-1i32) as u32)),
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
        left: &OldMachineTerm,
        right: &OldMachineTerm,
    ) -> Option<bool> {
        self.exact_signed_intervals_equal_views(
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        )
    }

    pub(super) fn exact_signed_intervals_equal_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<bool> {
        let (left_lower, left_upper) = self.signed_interval_view(left)?;
        let (right_lower, right_upper) = self.signed_interval_view(right)?;
        (left_lower == left_upper && right_lower == right_upper)
            .then_some(left_lower == right_lower)
    }

    /// The range of an `int64` term: its width range from the root
    /// constructor, narrowed by the constant `int64` order bounds indexed
    /// under the term or its canonical alias. These are keyed lookups on the
    /// queried term only, never a scan of the context. A term with neither a
    /// width range nor an indexed bound on both sides has no interval.
    pub(super) fn decide_indexed_greater_equal(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        // Preserve the native dispatcher's original admission scope. Reading
        // every native `constant <= term` here would add checked work before
        // its existing literal/identity routes (including during setup).
        if let OldConditionTerm::Compare { relation, .. } = condition
            && *relation != CompareRelation::GreaterEqual
        {
            return None;
        }
        let view = comparison_view(condition, true)?;
        if view.format != MachineIntegerType::Int32 || view.relation != Relation::LessEqual {
            return None;
        }
        // Normalized `constant <= operand`, including the Integer observation
        // spelling, reads precisely the operand's maintained extrema.
        let constant = view.operands[0].operand_view().word32_constant()? as i32 as i64;
        let (lower, upper) =
            self.indexed_constant_interval_view(view.operands[1].operand_view(), false)?;
        if upper < constant {
            Some(false)
        } else if lower >= constant {
            Some(true)
        } else {
            None
        }
    }

    // A clear-sign-bit mask has a local range. Keep comparison terms intact
    // so explicit arithmetic proofs retain their original proposition shapes.
    pub(super) fn decide_masked_order(&self, condition: &OldConditionTerm) -> Option<bool> {
        use crate::kernel::MachineOperandView;
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        fn range(term: MachineOperandView<'_>) -> Option<(i64, i64)> {
            if let Some(value) = term.word32_constant() {
                let value = value as i32 as i64;
                return Some((value, value));
            }
            let (format, MachineBinaryOp::BitwiseAnd, [a, b]) = term.binary()? else {
                return None;
            };
            if format.format().bits() != 32 {
                return None;
            }
            let mask = a.word32_constant().or_else(|| b.word32_constant())?;
            (mask <= i32::MAX as u32).then_some((0, mask as i64))
        }
        let query = comparison_view(condition, true)?;
        if query.format != MachineIntegerType::Int32 {
            return None;
        }
        let strict = match query.relation {
            Relation::Less => true,
            Relation::LessEqual => false,
            _ => return None,
        };
        let ((llo, lhi), (rlo, rhi)) = (
            range(query.operands[0].operand_view())?,
            range(query.operands[1].operand_view())?,
        );
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
    fn widened_unsigned_interval(
        &self,
        term: MachineOperandView<'_>,
        mut source: impl FnMut(MachineOperandView<'_>, bool),
    ) -> (i64, i64) {
        if let Some(value) = term.word32_constant() {
            return (value as i64, value as i64);
        }
        let mut range = (0, u32::MAX as i64);
        // The `uint32` widening of an unsigned 8- or 16-bit value is in its
        // source's range (the format's own range, no fact read).
        if let Some((MachineCastSpelling::Generic, source, _, _)) = term.cast()
            && source.format().bits() < 32
            && !source.format().is_signed()
        {
            range.1 = i64::try_from(source.format().bounds().1).unwrap_or(range.1);
        }
        if let Some((lo, hi)) = self.indexed_constant_interval_view(term, true) {
            source(term, true);
            range.0 = range.0.max(lo);
            range.1 = range.1.min(hi);
        }
        let sibling = Self::int32_widening_sibling_view(term);
        for term in std::iter::once(term).chain(sibling.as_ref().map(|s| s.operand_view())) {
            if let Some((lo, hi)) = self.indexed_constant_interval_view(term, false)
                && (lo >= 0 || range.1 <= i32::MAX as i64)
            {
                source(term, false);
                range.0 = range.0.max(lo);
                range.1 = range.1.min(hi);
            }
        }
        range
    }

    fn int32_widening_sibling_view(
        term: MachineOperandView<'_>,
    ) -> Option<crate::kernel::SharedMachineIntegerTerm> {
        use crate::kernel::{MachineCastSpelling as E, SharedMachineIntegerTerm};
        let (E::Generic, source, MachineIntegerType::UInt32, value) = term.cast()? else {
            return None;
        };
        if source.format().bits() >= 32 {
            return None;
        }
        Some(match value {
            MachineOperandView::Shared(root) => SharedMachineIntegerTerm::from_shared(
                MachineIntegerType::Int32,
                root.checking_machine_cast(source, MachineIntegerType::Int32),
            )
            .expect("shared cast operand"),
            MachineOperandView::Old(value) => SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                OldMachineTerm::machine_integer_cast(
                    source,
                    MachineIntegerType::Int32,
                    value.clone(),
                ),
            ),
        })
    }

    fn widened_unsigned_operand_view(
        term: MachineOperandView<'_>,
    ) -> Option<Option<MachineOperandView<'_>>> {
        if let Some((MachineCastSpelling::Int64FromUInt32, _, _, value)) = term.cast() {
            return Some(Some(value));
        }
        match term.literal()? {
            int64_constant!(value) if (0..=u32::MAX as i64).contains(&constant_i64(value)) => {
                Some(None)
            }
            _ => None,
        }
    }

    pub(crate) fn widened_unsigned_sum_bound_premises(
        &self,
        condition: &OldConditionTerm,
    ) -> Option<Vec<Proposition>> {
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let query = comparison_view(condition, true)?;
        if query.format != MachineIntegerType::Int64 || query.relation != Relation::LessEqual {
            return None;
        }
        let (MachineIntegerType::Int64, MachineBinaryOp::Add, [a, b]) =
            query.operands[0].operand_view().binary()?
        else {
            return None;
        };
        let operands = [
            Self::widened_unsigned_operand_view(a)?,
            Self::widened_unsigned_operand_view(b)?,
        ];
        let mut premises = Vec::new();
        for operand in operands.into_iter().flatten() {
            self.widened_unsigned_interval(operand, |term, unsigned| {
                let sources = match term {
                    MachineOperandView::Old(term) => {
                        let canonical = crate::kernel::eval::canonical_term(term);
                        self.checked_order_bounds
                            .interval_sources_view(MachineOperandView::Old(&canonical), unsigned)
                    }
                    MachineOperandView::Shared(_) => self
                        .checked_order_bounds
                        .interval_sources_view(term, unsigned),
                };
                premises.extend(sources.into_iter().flatten());
            });
        }
        Some(premises)
    }

    pub(crate) fn decide_widened_sum_bound(&self, condition: &OldConditionTerm) -> Option<bool> {
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let query = comparison_view(condition, true)?;
        if query.format != MachineIntegerType::Int64 || query.relation != Relation::LessEqual {
            return None;
        }
        let (MachineIntegerType::Int64, MachineBinaryOp::Add, [a, b]) =
            query.operands[0].operand_view().binary()?
        else {
            return None;
        };
        let a_operand = Self::widened_unsigned_operand_view(a)?;
        let b_operand = Self::widened_unsigned_operand_view(b)?;
        let bound = query.operands[1].operand_view().int64_constant()?;
        let interval = |term: MachineOperandView<'_>, operand: Option<MachineOperandView<'_>>| {
            if let Some(operand) = operand {
                self.widened_unsigned_interval(operand, |_, _| {})
            } else {
                let value = term.int64_constant().expect("checked widened constant");
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

    pub(super) fn int64_interval(&self, term: &OldMachineTerm) -> Option<(i64, i64)> {
        self.int64_interval_view(MachineOperandView::Old(term))
    }

    pub(super) fn int64_interval_view(&self, term: MachineOperandView<'_>) -> Option<(i64, i64)> {
        if let Some(bits) = self.wide_constant_from_equalities_view(term) {
            let value = bits as i64;
            return Some((value, value));
        }
        let (mut lower, mut upper) = term.int64_width_interval().unwrap_or((i64::MIN, i64::MAX));
        let canonical = match term {
            MachineOperandView::Old(term) => Some(crate::kernel::eval::canonical_term(term)),
            _ => None,
        };
        let mut keys = vec![term];
        if let (MachineOperandView::Old(written), Some(canonical)) = (term, canonical.as_ref())
            && written != canonical
        {
            keys.push(MachineOperandView::Old(canonical));
        }
        for key in keys {
            if let Some((direct_lower, direct_upper)) =
                self.checked_order_bounds.signed_wide_interval_view(key)
            {
                lower = lower.max(direct_lower);
                upper = upper.min(direct_upper);
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
        term: &OldMachineTerm,
    ) -> Vec<Proposition> {
        use crate::kernel::proof::arithmetic_special::signed_width_constant;
        let mut facts = Vec::new();
        let index = match width {
            SignedDefinedWidth::Int32 => &self.signed_order_bounds,
            SignedDefinedWidth::Int64 => &self.int64_signed_order_bounds,
        };
        if let Some(bounds) = index.get(term) {
            use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
            let format = match width {
                SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
                SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
            };
            let queried = Key::for_format(format, MachineOperandView::Old(term));
            for (endpoint, other, _, _, source) in bounds.sourced_operands() {
                crate::instrumentation::record_deterministic_work(1);
                let constant = match width {
                    SignedDefinedWidth::Int32 => other.word32_constant().is_some(),
                    SignedDefinedWidth::Int64 => other.int64_constant().is_some(),
                };
                if constant && Key::for_format(format, endpoint) == queried {
                    facts.push(source.clone());
                }
            }
        }
        if let Some(equalities) = self.equality_graph.exact_literal_sources(term) {
            crate::instrumentation::record_deterministic_work(equalities.len().max(1));
            for condition in equalities.keys() {
                let sides = match (width, condition) {
                    (
                        SignedDefinedWidth::Int32,
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::Equal,
                            left,
                            right,
                        },
                    )
                    | (
                        SignedDefinedWidth::Int64,
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left,
                            right,
                        },
                    ) => Some((left, right)),
                    _ => None,
                };
                if let Some((left, right)) = sides
                    && (left.as_ref() == term && signed_width_constant(width, right).is_some()
                        || right.as_ref() == term && signed_width_constant(width, left).is_some())
                {
                    facts.push(Proposition::condition_is(condition.clone(), true));
                }
            }
        }
        facts
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
    pub(super) fn decide_signed_order_from_conditional_interval_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        strict: bool,
    ) -> Option<bool> {
        let left = opaque_operand(left);
        let right = opaque_operand(right);
        if left.conditional_view().is_none() && right.conditional_view().is_none() {
            return None;
        }
        let (left_lower, left_upper) = self.signed_interval_view(left)?;
        let (right_lower, right_upper) = self.signed_interval_view(right)?;
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
    /// not to overflow ([`Self::signed_interval_from_operands_view`]); this makes
    /// nested bounds safe to reuse.
    ///
    /// A range is a range of the *value*, and a bound recorded on a compound
    /// term bounds its wrapped value: `0 <= (a - b) <= 10` holds of the
    /// wrapped difference of `INT_MIN` and `INT_MAX - 4`. So a range here is
    /// never evidence that the term's own operation does not overflow; that
    /// question is [`Self::signed_interval_from_operands_view`].
    pub(in crate::kernel) fn signed_interval(&self, term: &OldMachineTerm) -> Option<(i64, i64)> {
        self.signed_interval_view(MachineOperandView::Old(term))
    }

    pub(in crate::kernel) fn signed_interval_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<(i64, i64)> {
        // A shared operand is a DAG entry point even when no outer decision
        // established a scope. Nested queries reuse this borrowed context id.
        let _scope = matches!(term, MachineOperandView::Shared(_))
            .then(|| PureFactContextIdScope::enter(self));
        // Successful ranges and completed refusals depend only on the fact
        // set and operand. Memoize both so successive shared prefixes do not
        // revisit an overflowing subtree. Interrupted queries remain uncached.
        // Shared keys retain syntax identity; legacy keys keep their spelling.
        let key = ambient_assumptions_memo_id(self).map(|id| {
            (
                id,
                match term {
                    MachineOperandView::Old(term) => {
                        SignedIntervalOperandKey::Written(term.clone())
                    }
                    MachineOperandView::Shared(term) => {
                        SignedIntervalOperandKey::Shared(term.clone())
                    }
                },
            )
        });
        if let Some(hit) = key
            .as_ref()
            .and_then(|key| SIGNED_INTERVAL_MEMO.with(|memo| memo.borrow().get(key).copied()))
        {
            return hit;
        }
        let epoch = INCOMPLETE_REASONING_EPOCH.with(Cell::get);
        let result = self.signed_interval_uncached(term);
        if let Some(key) = key
            && (result.is_some() || INCOMPLETE_REASONING_EPOCH.with(Cell::get) == epoch)
        {
            SIGNED_INTERVAL_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= SIGNED_INTERVAL_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(key, result);
            });
        }
        result
    }

    /// [`Self::signed_interval`] with each endpoint moved past the values an
    /// exact fact says `term` is not: `0 <= x <= 3` with `x != 1`, `x != 2`
    /// and `x != 3` is `[0, 0]`. Maintained contiguous runs skip any number
    /// of written exclusions in one lookup; inferred endpoint exclusions get
    /// one fixed inference per end, without following another chain.
    pub(in crate::kernel) fn signed_interval_past_exclusions(
        &self,
        term: &OldMachineTerm,
    ) -> Option<(i64, i64)> {
        self.signed_interval_past_exclusions_view(MachineOperandView::Old(term))
    }

    pub(in crate::kernel) fn signed_interval_past_exclusions_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<(i64, i64)> {
        let (lower, upper) = self.signed_interval_view(term)?;
        let canonical;
        let indexed = match term {
            MachineOperandView::Old(term) => {
                canonical = crate::kernel::eval::canonical_term(term);
                MachineOperandView::Old(&canonical)
            }
            MachineOperandView::Shared(_) => term,
        };
        let (mut lower, mut upper) = self
            .checked_scalar_facts
            .past_exclusions(indexed, lower, upper);
        let excluded = |value: i64| {
            crate::instrumentation::record_deterministic_work(1);
            self.has_condition_fact(
                match term {
                    MachineOperandView::Old(term) => OldConditionTerm::equal(
                        term.clone(),
                        OldMachineTerm::constant(value as i32 as u32),
                    ),
                    MachineOperandView::Shared(_) => OldConditionTerm::integer_equal(
                        IntegerTerm::Machine(term.retain(MachineIntegerType::Int32)),
                        IntegerTerm::constant(value.into()),
                    ),
                },
                false,
            )
        };
        if lower < upper && excluded(lower) {
            lower += 1;
        }
        if lower < upper && excluded(upper) {
            upper -= 1;
        }
        Some((lower, upper))
    }

    /// The interval is reconstructed over the term's structure, so the walk
    /// is finite with no depth cut: each arithmetic node ranges its operands.
    fn signed_interval_uncached(&self, term: MachineOperandView<'_>) -> Option<(i64, i64)> {
        let term = opaque_operand(term);
        use crate::kernel::{MachineBinaryOp as Op, MachineCastSpelling as E};
        if let Some(value) = self.signed_constant_known_equal_view(term) {
            return Some((value, value));
        }
        let (mut lower, mut upper) = self
            .equality_graph
            .signed_int32_interval_view(term)
            .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
        if lower != i64::from(i32::MIN) && upper != i64::from(i32::MAX) {
            return Some((lower, upper));
        }
        let canonical;
        let indexed = match term {
            MachineOperandView::Old(term) => {
                canonical = crate::kernel::eval::canonical_term(term);
                MachineOperandView::Old(&canonical)
            }
            MachineOperandView::Shared(_) => term,
        };
        if let Some((lo, hi)) = self.checked_order_bounds.interval_with_strict_view(indexed) {
            lower = lower.max(lo);
            upper = upper.min(hi);
        }
        if lower != i64::from(i32::MIN) && upper != i64::from(i32::MAX) {
            return (lower <= upper).then_some((lower, upper));
        }
        if let Some((format, op, [left, right])) = term.binary()
            && format.format().bits() == 32
        {
            if matches!(op, Op::Add | Op::Subtract | Op::Multiply) {
                return self.signed_interval_from_operands_view(term);
            }
            if op == Op::BitwiseAnd
                && let Some(mask) = [left, right]
                    .into_iter()
                    .filter_map(|operand| operand.word32_constant().map(|v| i64::from(v as i32)))
                    .filter(|mask| *mask >= 0)
                    .min()
            {
                let (lo, hi) = (lower.max(0), upper.min(mask));
                return (lo <= hi).then_some((lo, hi));
            }
        }
        if let Some((E::Generic, source, destination, operand)) = term.cast() {
            if source == MachineIntegerType::UInt8 && destination == MachineIntegerType::Int8 {
                let (lo, hi) = self
                    .signed_interval_view(operand)
                    .map(|(lo, hi)| (lo.max(0), hi.min(255)))
                    .unwrap_or((0, 255));
                let (lo, hi) = if hi <= 127 {
                    (lo, hi)
                } else if lo >= 128 {
                    (lo - 256, hi - 256)
                } else {
                    (-128, 127)
                };
                return (lo <= hi).then_some((lo, hi));
            }
            if crate::kernel::primitives::is_narrow_widening32(source, destination) {
                let (min, max) = source.format().bounds();
                let (lo, hi) = (
                    lower.max(i64::try_from(min).expect("narrow bound")),
                    upper.min(i64::try_from(max).expect("narrow bound")),
                );
                return (lo <= hi).then_some((lo, hi));
            }
            if let Some((lo, hi)) = self.narrowed_cast_interval_view(term) {
                let (lo, hi) = (lower.max(lo), upper.min(hi));
                return (lo <= hi).then_some((lo, hi));
            }
        }
        if let Some((_, [left, right])) = term.conditional_view() {
            let (a, b) = self.signed_interval_view(left)?;
            let (c, d) = self.signed_interval_view(right)?;
            return Some((a.min(c), b.max(d)));
        }
        if let MachineOperandView::Old(term) = term
            && let Some(resolved) = self.resolve_memory_load_term(term)
            && resolved != *term
            && let Some((lo, hi)) = self
                .checked_order_bounds
                .interval_with_strict(&crate::kernel::eval::canonical_term(&resolved))
        {
            lower = lower.max(lo);
            upper = upper.min(hi);
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
    pub(in crate::kernel) fn signed_interval_from_operands_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<(i64, i64)> {
        let (lower, upper) = self.integer_interval_from_operands(term)?;
        (i128::from(i32::MIN) <= lower && upper <= i128::from(i32::MAX))
            .then_some((lower as i64, upper as i64))
    }

    /// The integer range of an addition, subtraction or multiplication of
    /// two 32-bit words, from the operands' signed value ranges, with
    /// nothing wrapped. `None` for any other term or an operand with no range.
    fn integer_interval_from_operands(&self, term: MachineOperandView<'_>) -> Option<(i128, i128)> {
        use crate::kernel::MachineBinaryOp as Op;
        let (format, op, [left, right]) = term.binary()?;
        if format.format().bits() != 32 || !matches!(op, Op::Add | Op::Subtract | Op::Multiply) {
            return None;
        }
        let (a, b) = self.signed_interval_view(left)?;
        let (c, d) = self.signed_interval_view(right)?;
        let (a, b, c, d) = (i128::from(a), i128::from(b), i128::from(c), i128::from(d));
        Some(match op {
            Op::Add => (a + c, b + d),
            Op::Subtract => (a - d, b - c),
            Op::Multiply => {
                let values = [a * c, a * d, b * c, b * d];
                (*values.iter().min()?, *values.iter().max()?)
            }
            _ => unreachable!(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_signed_ranges_preserve_wrapping_and_cast_rules() {
        use crate::kernel::{KernelTermImport, MachineBinaryOp, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let x = OldMachineTerm::Variable(Variable(994701));
        let facts = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_less_equal(OldMachineTerm::constant(2), x.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(x.clone(), OldMachineTerm::constant(4)),
                true,
            );
        for (op, expected) in [
            (MachineBinaryOp::Add, (4, 8)),
            // The word equality graph now retains x - x = 0.
            (MachineBinaryOp::Subtract, (0, 0)),
            (MachineBinaryOp::Multiply, (4, 16)),
            (MachineBinaryOp::BitwiseAnd, (0, 7)),
        ] {
            let right = if op == MachineBinaryOp::BitwiseAnd {
                OldMachineTerm::constant(7)
            } else {
                x.clone()
            };
            let written = OldMachineTerm::Binary {
                format: ty,
                op,
                left: Box::new(x.clone()),
                right: Box::new(right),
            };
            let root = KernelTermImport::default()
                .machine_arithmetic(ty, &written)
                .unwrap();
            let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
            assert_eq!(
                facts.signed_interval_view(operand.operand_view()),
                Some(expected)
            );
            assert!(!operand.has_boxed_operand());
            // The legacy interval adapter computes operand ranges directly;
            // the shared query also consults the retained word equality.
            let legacy_expected = if op == MachineBinaryOp::Subtract {
                (-2, 2)
            } else {
                expected
            };
            assert_eq!(facts.signed_interval(&written), Some(legacy_expected));
            if op == MachineBinaryOp::Subtract {
                // Operand-only overflow ranges still ignore correlation.
                assert_eq!(
                    facts.signed_interval_from_operands_view(operand.operand_view()),
                    Some((-2, 2))
                );
            }
        }
        for (source, destination, expected) in [
            (MachineIntegerType::UInt8, MachineIntegerType::Int8, (2, 4)),
            (
                MachineIntegerType::UInt8,
                MachineIntegerType::Int32,
                (0, 255),
            ),
            (MachineIntegerType::Int32, MachineIntegerType::UInt8, (2, 4)),
        ] {
            let written = OldMachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: source,
                to: destination,
                value: Box::new(x.clone()),
            };
            let root = KernelTermImport::default()
                .machine_arithmetic(destination, &written)
                .unwrap();
            assert_eq!(
                facts.signed_interval_view(MachineOperandView::Shared(&root)),
                Some(expected)
            );
            assert_eq!(facts.signed_interval(&written), Some(expected));
        }
        let written = OldMachineTerm::add(x.clone(), OldMachineTerm::constant(1));
        let root = KernelTermImport::default()
            .machine_arithmetic(ty, &written)
            .unwrap();
        let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let wrapped = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::equal(x, OldMachineTerm::constant(i32::MAX as u32)),
                true,
            )
            .assume_condition(
                OldConditionTerm::integer_equal(
                    IntegerTerm::Machine(operand.clone()),
                    IntegerTerm::constant(i32::MIN.into()),
                ),
                true,
            );
        assert_eq!(
            wrapped.signed_interval_view(operand.operand_view()),
            Some((i64::from(i32::MIN), i64::from(i32::MIN)))
        );
        assert_eq!(
            wrapped.signed_interval_from_operands_view(operand.operand_view()),
            None
        );
        assert!(!operand.has_boxed_operand());
    }

    #[test]
    fn int32_division_overflow_is_decided_from_operand_intervals_and_disequalities() {
        let x = OldMachineTerm::Variable(Variable(95_201));
        let y = OldMachineTerm::Variable(Variable(95_202));
        let constant = |value: i32| OldMachineTerm::constant(value as u32);
        let divide = OldConditionTerm::signed_divide_overflows(x.clone(), y.clone());
        assert_eq!(PureFactContext::new().decide(&divide), None);
        // `y != 0` alone leaves `INT_MIN / -1` open.
        let nonzero = PureFactContext::new()
            .assume_condition(OldConditionTerm::equal(y.clone(), constant(0)), false);
        assert_eq!(nonzero.decide(&divide), None);
        // A divisor range without `-1`, on either side of it.
        let positive = nonzero.clone().assume_condition(
            OldConditionTerm::signed_greater_than(y.clone(), constant(0)),
            true,
        );
        assert_eq!(positive.decide(&divide), Some(false));
        let below = PureFactContext::new().assume_condition(
            OldConditionTerm::signed_less_than(y.clone(), constant(-1)),
            true,
        );
        assert_eq!(below.decide(&divide), Some(false));
        // A dividend range without `INT_MIN`.
        let nonnegative = nonzero.clone().assume_condition(
            OldConditionTerm::signed_greater_equal(x.clone(), constant(0)),
            true,
        );
        assert_eq!(nonnegative.decide(&divide), Some(false));
        // A disequality on either operand's one overflowing value.
        let not_minus_one = nonzero
            .clone()
            .assume_condition(OldConditionTerm::equal(y.clone(), constant(-1)), false);
        assert_eq!(not_minus_one.decide(&divide), Some(false));
        let not_int_min = nonzero.clone().assume_condition(
            OldConditionTerm::equal(x.clone(), constant(i32::MIN)),
            false,
        );
        assert_eq!(not_int_min.decide(&divide), Some(false));
        // The exact exclusion as one disjunction, in either arm order.
        let dividend_differs = Proposition::condition_is(
            OldConditionTerm::equal(x.clone(), constant(i32::MIN)),
            false,
        );
        let divisor_differs =
            Proposition::condition_is(OldConditionTerm::equal(y.clone(), constant(-1)), false);
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
            OldConditionTerm::signed_less_equal(y.clone(), constant(5)),
            true,
        );
        assert_eq!(wide.decide(&divide), None);
        let other_value =
            nonzero.assume_condition(OldConditionTerm::equal(x.clone(), constant(7)), false);
        assert_eq!(other_value.decide(&divide), None);
        // The overflowing pair itself is never decided defined.
        let exceptional = PureFactContext::new()
            .assume_condition(OldConditionTerm::equal(x.clone(), constant(i32::MIN)), true)
            .assume_condition(OldConditionTerm::equal(y, constant(-1)), true);
        assert_ne!(exceptional.decide(&divide), Some(false));
    }

    #[test]
    fn int32_negation_overflow_is_excluded_by_a_disequality_at_int_min() {
        let x = OldMachineTerm::Variable(Variable(95_301));
        let constant = |value: i32| OldMachineTerm::constant(value as u32);
        // Unary minus lowers to `0 - x`.
        let negate = OldConditionTerm::signed_subtract_overflows(constant(0), x.clone());
        assert_eq!(PureFactContext::new().decide(&negate), None);
        let excluded = PureFactContext::new().assume_condition(
            OldConditionTerm::equal(x.clone(), constant(i32::MIN)),
            false,
        );
        assert_eq!(excluded.decide(&negate), Some(false));
        let above = PureFactContext::new().assume_condition(
            OldConditionTerm::signed_greater_than(x.clone(), constant(i32::MIN)),
            true,
        );
        assert_eq!(above.decide(&negate), Some(false));
        // Excluding another value leaves `INT_MIN` open.
        let other_value = PureFactContext::new()
            .assume_condition(OldConditionTerm::equal(x.clone(), constant(0)), false);
        assert_eq!(other_value.decide(&negate), None);
        // The exclusion moves the operand's range by one, no further.
        assert_eq!(
            excluded.decide(&OldConditionTerm::signed_subtract_overflows(
                x.clone(),
                constant(1)
            )),
            Some(false)
        );
        assert_eq!(
            excluded.decide(&OldConditionTerm::signed_subtract_overflows(x, constant(2))),
            None
        );
    }

    #[test]
    fn equal_value_intervals_intersect_and_stay_branch_local() {
        let x = OldMachineTerm::Variable(Variable(190_001));
        let y = OldMachineTerm::Variable(Variable(190_002));
        let parent = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_greater_equal(x.clone(), 0u32.into()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(y.clone(), 10u32.into()),
                true,
            );
        let branch = parent
            .clone()
            .assume_condition(OldConditionTerm::equal(x.clone(), y.clone()), true);
        assert_eq!(branch.signed_interval(&x), Some((0, 10)));
        assert_eq!(branch.signed_interval(&y), Some((0, 10)));
        assert_eq!(parent.signed_interval(&x), Some((0, i64::from(i32::MAX))));
        assert_eq!(parent.signed_interval(&y), Some((i64::from(i32::MIN), 10)));
        let impossible =
            branch.assume_condition(OldConditionTerm::equal(x.clone(), y.clone()), false);
        assert!(impossible.is_inconsistent());
        assert_eq!(impossible.signed_interval(&x), Some((0, 10)));
        assert_eq!(impossible.signed_interval(&y), Some((0, 10)));
        let sibling = parent.assume_condition(OldConditionTerm::equal(x.clone(), y.clone()), false);
        assert!(!sibling.is_inconsistent());
        assert_eq!(sibling.signed_interval(&x), Some((0, i64::from(i32::MAX))));
        assert_eq!(sibling.signed_interval(&y), Some((i64::from(i32::MIN), 10)));
    }

    #[test]
    fn equal_value_intervals_preserve_signed_order_and_width() {
        let x = OldMachineTerm::Variable(Variable(190_011));
        let y = OldMachineTerm::Variable(Variable(190_012));
        for (condition, value, expected) in [
            (
                OldConditionTerm::signed_less_than(x.clone(), 10u32.into()),
                true,
                (i64::from(i32::MIN), 9),
            ),
            (
                OldConditionTerm::signed_less_than(x.clone(), 10u32.into()),
                false,
                (10, i64::from(i32::MAX)),
            ),
            (
                OldConditionTerm::signed_less_equal(x.clone(), 10u32.into()),
                false,
                (11, i64::from(i32::MAX)),
            ),
            (
                OldConditionTerm::signed_greater_than(x.clone(), 10u32.into()),
                true,
                (11, i64::from(i32::MAX)),
            ),
            (
                OldConditionTerm::signed_greater_equal(x.clone(), 10u32.into()),
                false,
                (i64::from(i32::MIN), 9),
            ),
        ] {
            let facts = PureFactContext::new()
                .assume_condition(condition, value)
                .assume_condition(OldConditionTerm::equal(x.clone(), y.clone()), true);
            assert_eq!(facts.signed_interval(&y), Some(expected));
        }
        let wide = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::int64_signed_greater_equal(
                    x.clone(),
                    OldMachineTerm::int64_constant(0),
                ),
                true,
            )
            .assume_condition(
                OldConditionTerm::int64_signed_less_equal(
                    x.clone(),
                    OldMachineTerm::int64_constant(10),
                ),
                true,
            )
            .assume_condition(OldConditionTerm::int64_equal(x.clone(), y.clone()), true);
        assert_eq!(
            wide.signed_interval(&y),
            Some((i64::from(i32::MIN), i64::from(i32::MAX)))
        );
    }

    #[test]
    fn exact_signed_bounds_avoid_context_scan() {
        let x = OldMachineTerm::Variable(Variable(91_001));
        let y = OldMachineTerm::Variable(Variable(91_002));
        let mut assumptions = PureFactContext::new();
        for index in 0..128 {
            let unrelated = OldMachineTerm::Variable(Variable(92_000 + index));
            assumptions = assumptions.assume_condition(
                OldConditionTerm::signed_less_equal(unrelated, OldMachineTerm::constant(1_000)),
                true,
            );
        }
        for term in [x.clone(), y.clone()] {
            assumptions = assumptions
                .assume_condition(
                    OldConditionTerm::signed_greater_equal(
                        term.clone(),
                        OldMachineTerm::constant(0),
                    ),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_equal(term, OldMachineTerm::constant(1_000)),
                    true,
                );
        }

        PureFactContext::reset_signed_interval_fallback_fact_visits();
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_add_overflows(x, y)),
            Some(false)
        );
        assert_eq!(PureFactContext::signed_interval_fallback_fact_visits(), 0);
    }

    /// Interval checking requires the intermediate endpoint bound explicitly;
    /// it does not reconstruct a bound by walking symbolic order facts.
    #[test]
    fn an_order_chain_requires_an_explicit_increment_bound() {
        let i = OldMachineTerm::Variable(Variable(96_001));
        let j = OldMachineTerm::Variable(Variable(96_002));
        let lower_and_link = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_less_equal(OldMachineTerm::constant(0), i.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(i.clone(), j.clone()),
                true,
            );
        let bounded = lower_and_link.clone().assume_condition(
            OldConditionTerm::signed_less_than(j.clone(), OldMachineTerm::constant(1000)),
            true,
        );
        let increment =
            OldConditionTerm::signed_add_overflows(i.clone(), OldMachineTerm::constant(1));
        assert_eq!(bounded.signed_interval(&i), Some((0, i64::from(i32::MAX))));
        let bounded = bounded.assume_condition(
            OldConditionTerm::signed_less_than(i.clone(), OldMachineTerm::constant(1000)),
            true,
        );
        assert_eq!(bounded.decide(&increment), Some(false));
        assert_eq!(bounded.signed_interval(&i), Some((0, 999)));
        assert_eq!(
            bounded.decide(&OldConditionTerm::signed_subtract_overflows(
                i.clone(),
                OldMachineTerm::constant(1)
            )),
            Some(false)
        );
        // `j` unbounded: `i` may be INT32_MAX.
        assert_eq!(lower_and_link.decide(&increment), None);
        // A chain ending at a constant that leaves no room is no bound.
        let at_max = lower_and_link.clone().assume_condition(
            OldConditionTerm::signed_less_equal(
                j.clone(),
                OldMachineTerm::constant(i32::MAX as u32),
            ),
            true,
        );
        assert_eq!(at_max.decide(&increment), None);
        // The lower direction: `-5 < k <= i`, `i <= 10` ranges `k - 1`.
        let k = OldMachineTerm::Variable(Variable(96_003));
        let below = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_less_than(
                    OldMachineTerm::constant((-5i32) as u32),
                    k.clone(),
                ),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(k.clone(), i.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(i.clone(), OldMachineTerm::constant(10)),
                true,
            );
        assert_eq!(below.signed_interval(&k), Some((-4, i64::from(i32::MAX))));
        let below = below.assume_condition(
            OldConditionTerm::signed_less_equal(k.clone(), OldMachineTerm::constant(10)),
            true,
        );
        assert_eq!(below.signed_interval(&k), Some((-4, 10)));
        // A lower chain needs a constant below: `m <= k` alone leaves `m`
        // at INT32_MIN possible.
        let m = OldMachineTerm::Variable(Variable(96_004));
        let unbounded_below = below.assume_condition(
            OldConditionTerm::signed_less_equal(m.clone(), k.clone()),
            true,
        );
        assert_eq!(
            unbounded_below.decide(&OldConditionTerm::signed_subtract_overflows(
                m,
                OldMachineTerm::constant(1)
            )),
            None
        );
    }

    #[test]
    fn bounded_nested_increment_uses_reconstructed_interval() {
        let x = OldMachineTerm::Variable(Variable(93_001));
        let once = OldMachineTerm::add(x.clone(), OldMachineTerm::constant(1));
        let assumptions = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_greater_equal(x.clone(), OldMachineTerm::constant(0)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(x, OldMachineTerm::constant(2147483645)),
                true,
            );

        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_add_overflows(
                once,
                OldMachineTerm::constant(1),
            )),
            Some(false)
        );
    }

    #[test]
    fn compound_add_bounds_are_used_before_reconstruction() {
        let x = OldMachineTerm::Variable(Variable(93_003));
        let compound = OldMachineTerm::add(x, OldMachineTerm::constant(1));
        let assumptions = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_greater_equal(
                    compound.clone(),
                    OldMachineTerm::constant(0),
                ),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(
                    compound.clone(),
                    OldMachineTerm::constant(2147483645),
                ),
                true,
            );

        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_add_overflows(
                compound,
                OldMachineTerm::constant(2),
            )),
            Some(false)
        );
    }

    #[test]
    fn insufficient_nested_increment_bound_does_not_rule_out_overflow() {
        let x = OldMachineTerm::Variable(Variable(93_002));
        let once = OldMachineTerm::add(x.clone(), OldMachineTerm::constant(1));
        let assumptions = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_greater_equal(x.clone(), OldMachineTerm::constant(0)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(x, OldMachineTerm::constant(2147483646)),
                true,
            );

        assert_ne!(
            assumptions.decide(&OldConditionTerm::signed_add_overflows(
                once,
                OldMachineTerm::constant(1),
            )),
            Some(false)
        );
    }

    #[test]
    fn bounded_multiplication_uses_operand_intervals() {
        let x = OldMachineTerm::Variable(Variable(93_004));
        let y = OldMachineTerm::Variable(Variable(93_005));
        let assumptions = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_greater_equal(x.clone(), OldMachineTerm::constant(0)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(x, OldMachineTerm::constant(100)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_greater_equal(y.clone(), OldMachineTerm::constant(0)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(y.clone(), OldMachineTerm::constant(100)),
                true,
            );

        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_multiply_overflows(
                OldMachineTerm::Variable(Variable(93_004)),
                OldMachineTerm::Variable(Variable(93_005)),
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
        let a = OldMachineTerm::Variable(Variable(93_010));
        let b = OldMachineTerm::Variable(Variable(93_011));
        for result in [
            binary_node!(Int32, Subtract, Box::new(a.clone()), Box::new(b.clone())),
            binary_node!(Int32, Multiply, Box::new(a.clone()), Box::new(b.clone())),
        ] {
            let assumptions = PureFactContext::new()
                .assume_condition(
                    OldConditionTerm::signed_greater_equal(
                        result.clone(),
                        OldMachineTerm::constant(0),
                    ),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_equal(
                        result.clone(),
                        OldMachineTerm::constant(10),
                    ),
                    true,
                );
            let overflows = match &result {
                binary_term!(Int32, Subtract, ..) => {
                    OldConditionTerm::signed_subtract_overflows(a.clone(), b.clone())
                }
                _ => OldConditionTerm::signed_multiply_overflows(a.clone(), b.clone()),
            };
            assert_ne!(assumptions.decide(&overflows), Some(false), "{result:?}");
            assert_eq!(assumptions.signed_interval(&result), Some((0, 10)));
        }
    }

    fn indicator(variable: u64) -> OldMachineTerm {
        OldMachineTerm::If {
            condition: Box::new(OldConditionTerm::equal(
                OldMachineTerm::Variable(Variable(variable)),
                OldMachineTerm::constant(0),
            )),
            then_term: Box::new(OldMachineTerm::constant(1)),
            else_term: Box::new(OldMachineTerm::constant(0)),
        }
    }

    #[test]
    fn a_conditional_is_ranged_by_the_hull_of_its_arms() {
        let assumptions = PureFactContext::new();
        let indicator = indicator(93_006);

        // Both hull bounds are decided, with the condition left undecided.
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_less_equal(
                OldMachineTerm::constant(0),
                indicator.clone(),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_less_equal(
                indicator.clone(),
                OldMachineTerm::constant(1),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_greater_equal(
                indicator.clone(),
                OldMachineTerm::constant(0),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_less_than(
                indicator.clone(),
                OldMachineTerm::constant(2),
            )),
            Some(true)
        );

        // A bound that only one arm satisfies stays undecided, and one that
        // neither arm satisfies is decided false.
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_less_equal(
                indicator.clone(),
                OldMachineTerm::constant(0),
            )),
            None
        );
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_less_than(
                OldMachineTerm::constant(1),
                indicator,
            )),
            Some(false)
        );
    }

    #[test]
    fn a_conditional_over_bounded_variables_uses_their_intervals() {
        let x = OldMachineTerm::Variable(Variable(93_007));
        let assumptions = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_greater_equal(x.clone(), OldMachineTerm::constant(3)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(x.clone(), OldMachineTerm::constant(9)),
                true,
            );
        let conditional = OldMachineTerm::If {
            condition: Box::new(OldConditionTerm::equal(
                x.clone(),
                OldMachineTerm::constant(5),
            )),
            then_term: Box::new(x),
            else_term: Box::new(OldMachineTerm::constant(4)),
        };

        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_less_equal(
                OldMachineTerm::constant(3),
                conditional.clone(),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_less_equal(
                conditional.clone(),
                OldMachineTerm::constant(9),
            )),
            Some(true)
        );
        assert_eq!(
            assumptions.decide(&OldConditionTerm::signed_less_equal(
                conditional.clone(),
                OldMachineTerm::constant(8),
            )),
            None
        );
        let root = crate::kernel::KernelTerm::retained_machine_operand(
            MachineIntegerType::Int32,
            MachineOperandView::Old(&conditional),
        );
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        assert_eq!(
            assumptions.signed_interval_view(MachineOperandView::Shared(&root)),
            Some((3, 9))
        );
        for (limit, expected) in [(9, Some(true)), (8, None), (2, Some(false))] {
            let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::LessEqual,
                [
                    MachineOperandView::Shared(&root),
                    MachineOperandView::Old(&OldMachineTerm::constant(limit)),
                ],
            );
            assert_eq!(assumptions.decide(&condition), expected);
        }
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }

    #[test]
    fn widened_32_bit_operands_cannot_overflow_int64_addition() {
        let t = OldMachineTerm::int64_from_uint32(OldMachineTerm::Variable(Variable(94_001)));
        let x = OldMachineTerm::int64_from_32(OldMachineTerm::Variable(Variable(94_002)));
        let wide = OldMachineTerm::Variable(Variable(94_003));

        // The widening constructors alone range both operands.
        assert_eq!(
            OldConditionTerm::int64_signed_add_overflows(t.clone(), x.clone()),
            OldConditionTerm::Constant(false)
        );
        assert_eq!(
            OldConditionTerm::int64_signed_subtract_overflows(t.clone(), x.clone()),
            OldConditionTerm::Constant(false)
        );
        assert_eq!(
            OldConditionTerm::int64_signed_subtract_overflows(x.clone(), t.clone()),
            OldConditionTerm::Constant(false)
        );
        // A width range does not fit next to a constant at the int64 edge.
        let max = OldMachineTerm::int64_constant(i64::MAX);
        assert!(matches!(
            OldConditionTerm::int64_signed_add_overflows(t.clone(), max.clone()),
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Add,
                left: _,
                right: _
            }
        ));
        assert!(matches!(
            OldConditionTerm::int64_signed_add_overflows(x.clone(), max),
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Add,
                left: _,
                right: _
            }
        ));
        // An int64 atom has no width range of its own.
        let unbounded = OldConditionTerm::int64_signed_add_overflows(wide, t);
        assert!(matches!(
            unbounded,
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Add,
                left: _,
                right: _
            }
        ));
        assert_eq!(PureFactContext::new().decide(&unbounded), None);
    }

    #[test]
    fn int64_division_and_multiplication_guards_use_only_queried_bounds() {
        let n = OldMachineTerm::Variable(Variable(95_101));
        let d = OldMachineTerm::Variable(Variable(95_102));
        let constant = OldMachineTerm::int64_constant;
        let positive = PureFactContext::new().assume_condition(
            OldConditionTerm::int64_signed_greater_than(d.clone(), constant(0)),
            true,
        );
        let divide = OldConditionTerm::int64_signed_divide_overflows(n.clone(), d.clone());
        assert_eq!(positive.decide(&divide), Some(false));
        assert_eq!(
            positive.decide(&OldConditionTerm::int64_equal(d.clone(), constant(0))),
            Some(false)
        );
        assert_eq!(
            OldMachineTerm::int64_subtract(n.clone(), n.clone()),
            constant(0)
        );
        assert_eq!(PureFactContext::new().decide(&divide), None);
        let exact = PureFactContext::new()
            .assume_condition(OldConditionTerm::int64_equal(n.clone(), constant(7)), true)
            .assume_condition(OldConditionTerm::int64_equal(d.clone(), constant(3)), true);
        assert_eq!(exact.decide(&divide), Some(false));
        let exceptional = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::int64_equal(n.clone(), constant(i64::MIN)),
                true,
            )
            .assume_condition(OldConditionTerm::int64_equal(d.clone(), constant(-1)), true);
        assert_ne!(exceptional.decide(&divide), Some(false));
        assert_ne!(
            PureFactContext::new()
                .assume_condition(OldConditionTerm::int64_equal(d.clone(), constant(0)), true)
                .decide(&divide),
            Some(false)
        );
        let multiply = OldConditionTerm::int64_signed_multiply_overflows(constant(2), n.clone());
        let bounded = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::int64_signed_less_equal(constant(i64::MIN / 2), n.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::int64_signed_less_equal(n.clone(), constant(i64::MAX / 2)),
                true,
            );
        assert_eq!(bounded.decide(&multiply), Some(false));
        assert_eq!(PureFactContext::new().decide(&multiply), None);
        let same = OldConditionTerm::int64_signed_subtract_overflows(n.clone(), n.clone());
        assert_eq!(PureFactContext::new().decide(&same), Some(false));
    }

    #[test]
    fn int64_constant_division_and_remainder_are_partial_without_panicking() {
        let constant = OldMachineTerm::int64_constant;
        for (n, d, quotient, remainder) in [
            (7, 3, Some(2), Some(1)),
            (-7, 3, Some(-2), Some(-1)),
            (i64::MIN, -1, None, None),
            (7, 0, None, None),
        ] {
            assert_eq!(
                OldMachineTerm::int64_divide(constant(n), constant(d)).int64_as_const(),
                quotient
            );
            assert_eq!(
                OldMachineTerm::int64_remainder(constant(n), constant(d)).int64_as_const(),
                remainder
            );
        }
    }

    #[test]
    fn int64_order_bounds_decide_addition_and_subtraction_overflow() {
        let a = OldMachineTerm::Variable(Variable(95_001));
        let b = OldMachineTerm::Variable(Variable(95_002));
        let constant = OldMachineTerm::int64_constant;
        let half = 1i64 << 62;
        let bounded = |a_lower: i64, a_upper: i64, b_lower: i64, b_upper: i64| {
            PureFactContext::new()
                .assume_condition(
                    OldConditionTerm::int64_signed_less_equal(constant(a_lower), a.clone()),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::int64_signed_less_equal(a.clone(), constant(a_upper)),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::int64_signed_less_equal(constant(b_lower), b.clone()),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::int64_signed_less_equal(b.clone(), constant(b_upper)),
                    true,
                )
        };
        let add = OldConditionTerm::int64_signed_add_overflows(a.clone(), b.clone());
        let subtract = OldConditionTerm::int64_signed_subtract_overflows(a.clone(), b.clone());

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
                OldConditionTerm::int64_signed_less_equal(a.clone(), constant(1000)),
                true,
            )
            .assume_condition(
                OldConditionTerm::int64_signed_less_equal(b.clone(), constant(1000)),
                true,
            );
        assert_eq!(upper_only.decide(&add), None);

        // A false strict order is the reversed non-strict order: `!(a < 0)`
        // is `0 <= a`, and `!(1000 < a)` is `a <= 1000`.
        let negated = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::int64_signed_less_than(a.clone(), constant(0)),
                false,
            )
            .assume_condition(
                OldConditionTerm::int64_signed_less_than(constant(1000), a.clone()),
                false,
            )
            .assume_condition(
                OldConditionTerm::int64_signed_greater_equal(b.clone(), constant(0)),
                true,
            )
            .assume_condition(
                OldConditionTerm::int64_signed_greater_than(constant(1001), b.clone()),
                true,
            );
        assert_eq!(negated.decide(&add), Some(false));

        // Int32 order facts about the same term never bound it as an int64.
        let int32_bounded = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_less_equal(OldMachineTerm::constant(0), a.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(a.clone(), OldMachineTerm::constant(1000)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(OldMachineTerm::constant(0), b.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(b.clone(), OldMachineTerm::constant(1000)),
                true,
            );
        assert_eq!(int32_bounded.decide(&add), None);
    }

    fn boxed_masked_order_reference(condition: &OldConditionTerm) -> Option<bool> {
        fn range(term: &OldMachineTerm) -> Option<(i64, i64)> {
            if let Some(value) = term.as_const() {
                let value = value as i32 as i64;
                return Some((value, value));
            }
            let binary_term!(Bits32, BitwiseAnd, a, b) = term else {
                return None;
            };
            let mask = a.as_const().or_else(|| b.as_const())?;
            (mask <= i32::MAX as u32).then_some((0, mask as i64))
        }
        let (left, right, strict) = match condition {
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            } => (a, b, true),
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            } => (a, b, false),
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            } => (b, a, true),
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => (b, a, false),
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

    #[test]
    fn masked_comparison_views_preserve_written_verdicts() {
        let context = PureFactContext::new();
        for mask in [0, 127, i32::MAX as u32, u32::MAX] {
            let masked = OldMachineTerm::Binary {
                format: MachineIntegerType::Int32,
                op: MachineBinaryOp::BitwiseAnd,
                left: Box::new(OldMachineTerm::Variable(Variable(985301))),
                right: Box::new(OldMachineTerm::constant(mask)),
            };
            for bound in [0, 42, 128, u32::MAX] {
                for relation in [
                    CompareRelation::LessThan,
                    CompareRelation::LessEqual,
                    CompareRelation::GreaterThan,
                    CompareRelation::GreaterEqual,
                    CompareRelation::Equal,
                ] {
                    for (left, right) in [
                        (masked.clone(), OldMachineTerm::constant(bound)),
                        (OldMachineTerm::constant(bound), masked.clone()),
                    ] {
                        let query = OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation,
                            left: Box::new(left),
                            right: Box::new(right),
                        };
                        assert_eq!(
                            context.decide_masked_order(&query),
                            boxed_masked_order_reference(&query)
                        );
                    }
                }
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/overflow_intervals/tests.rs"
        );
    }
}

#[cfg(test)]
mod shared_widened_query_tests {
    use super::*;
    impl PureFactContext {
        fn reference_widened_unsigned_interval(&self, term: &OldMachineTerm) -> (i64, i64) {
            if let Some(value) = term.as_const() {
                return (value as i64, value as i64);
            }
            let mut range = (0, u32::MAX as i64);
            // The `uint32` widening of an unsigned 8- or 16-bit value is in its
            // source's range (the format's own range, no fact read).
            if let OldMachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: source,
                ..
            } = term
                && source.format().bits() < 32
                && !source.format().is_signed()
            {
                range.1 = i64::try_from(source.format().bounds().1).unwrap_or(range.1);
            }
            if let Some((lo, hi)) = self.indexed_unsigned32_constant_interval(term) {
                range.0 = range.0.max(lo);
                range.1 = range.1.min(hi);
            }
            let sibling = Self::reference_int32_widening_sibling(term);
            for term in std::iter::once(term).chain(sibling.as_ref()) {
                if let Some((lo, hi)) = self.indexed_constant_interval(term)
                    && (lo >= 0 || range.1 <= i32::MAX as i64)
                {
                    range.0 = range.0.max(lo);
                    range.1 = range.1.min(hi);
                }
            }
            range
        }

        fn reference_int32_widening_sibling(term: &OldMachineTerm) -> Option<OldMachineTerm> {
            let OldMachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: MachineIntegerType::UInt32,
            } = term
            else {
                return None;
            };
            (source.format().bits() < 32).then(|| {
                OldMachineTerm::machine_integer_cast(
                    *source,
                    MachineIntegerType::Int32,
                    value.as_ref().clone(),
                )
            })
        }

        fn reference_widened_unsigned_operand(
            term: &OldMachineTerm,
        ) -> Option<Option<&OldMachineTerm>> {
            match term {
                cast_term!(Int64FromUInt32, value) => Some(Some(value)),
                int64_constant!(value) if (0..=u32::MAX as i64).contains(&constant_i64(*value)) => {
                    Some(None)
                }
                _ => None,
            }
        }

        pub(crate) fn reference_decide_widened_sum_bound(
            &self,
            condition: &OldConditionTerm,
        ) -> Option<bool> {
            let OldConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } = condition
            else {
                return None;
            };
            let OldMachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Add,
                left: a,
                right: b,
            } = left.as_ref()
            else {
                return None;
            };
            let a_operand = Self::reference_widened_unsigned_operand(a)?;
            let b_operand = Self::reference_widened_unsigned_operand(b)?;
            let bound = right.int64_as_const()?;
            let interval = |term: &OldMachineTerm, operand: Option<&OldMachineTerm>| {
                if let Some(operand) = operand {
                    self.reference_widened_unsigned_interval(operand)
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
    }

    #[test]
    fn shared_widened_sum_queries_preserve_bounds_and_sources() {
        use crate::kernel::{IntegerTerm, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        let a = OldMachineTerm::Variable(Variable(986101));
        let b = OldMachineTerm::Variable(Variable(986102));
        let cases = [
            vec![],
            vec![
                OldConditionTerm::unsigned_less_equal(a.clone(), 100u32.into()),
                OldConditionTerm::unsigned_less_equal(b.clone(), 50u32.into()),
            ],
            vec![
                OldConditionTerm::signed_greater_equal(a.clone(), 0u32.into()),
                OldConditionTerm::signed_less_equal(a.clone(), 100u32.into()),
            ],
            vec![OldConditionTerm::unsigned_greater_equal(
                a.clone(),
                (u32::MAX - 100).into(),
            )],
        ];
        for facts in cases {
            let context = facts.iter().fold(PureFactContext::new(), |context, fact| {
                context.assume_condition(fact.clone(), true)
            });
            for first in [
                a.clone(),
                OldMachineTerm::machine_integer_cast(
                    MachineIntegerType::UInt8,
                    MachineIntegerType::UInt32,
                    a.clone(),
                ),
            ] {
                let sum = OldMachineTerm::int64_add(
                    OldMachineTerm::int64_from_uint32(first),
                    OldMachineTerm::int64_from_uint32(b.clone()),
                );
                for bound in [
                    -1,
                    0,
                    49,
                    100,
                    150,
                    i64::from(u32::MAX),
                    2 * i64::from(u32::MAX),
                ] {
                    let written = OldConditionTerm::int64_signed_less_equal(
                        sum.clone(),
                        OldMachineTerm::int64_constant(bound),
                    );
                    let expected = context.reference_decide_widened_sum_bound(&written);
                    assert_eq!(context.decide_widened_sum_bound(&written), expected);
                    let machine =
                        SharedMachineIntegerTerm::intern(MachineIntegerType::Int64, sum.clone());
                    let shared = OldConditionTerm::IntegerLessEqual(
                        IntegerTerm::Machine(machine.clone()).into(),
                        IntegerTerm::constant(bound.into()).into(),
                    );
                    assert_eq!(context.decide_widened_sum_bound(&shared), expected);
                    let selected = context
                        .widened_unsigned_sum_bound_premises(&shared)
                        .unwrap();
                    assert!(selected.len() <= 12);
                    assert!(selected.iter().all(|p| context.contains_assumed_exact(p)));
                    let selected_context = selected
                        .iter()
                        .fold(PureFactContext::new(), |context, fact| {
                            context.assume_proposition(fact.clone())
                        });
                    assert_eq!(selected_context.decide_widened_sum_bound(&shared), expected);
                }
            }
        }
    }
}

#[cfg(test)]
mod shared_overflow_query_tests {
    use super::*;
    use crate::kernel::machine_integer::{Operation, definedness};
    use crate::kernel::{KernelTermImport, SharedMachineIntegerTerm};

    fn query(
        format: MachineIntegerType,
        operation: Operation,
        operand: &SharedMachineIntegerTerm,
        right: IntegerTerm,
    ) -> definedness::OverflowQueryView {
        let exact = operation.exact(IntegerTerm::Machine(operand.clone()), right);
        definedness::overflow_query_of_integer_bound(
            &definedness::ordinary_bounds(format, exact)[0],
            std::iter::once(format),
        )
        .unwrap()
    }

    #[test]
    fn exact_signed_add_overflow_keeps_direct_sources_and_requires_both_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        let a = OldMachineTerm::Variable(Variable(983719));
        let b = OldMachineTerm::Variable(Variable(983720));
        let atom = OldConditionTerm::signed_add_overflows(a.clone(), b.clone());
        let parent = PureFactContext::new();
        for truth in [false, true] {
            let fact = Proposition::condition_is(atom.clone(), truth);
            let child = parent.clone().assume_proposition(fact.clone());
            let (answer, sources) = collect_consulted_premises(|| {
                capture_implicit_consulted_premises(|| child.exact_signed_add_overflow(&a, &b))
            });
            assert_eq!(answer, Some(truth));
            assert!(sources.contains(&fact));
        }
        let bounds =
            definedness::integer_bounds_of_definedness(&Proposition::condition_is(atom, false));
        assert_eq!(bounds.len(), 2);
        let upper = parent.clone().assume_proposition(bounds[0].clone());
        assert_eq!(upper.exact_signed_add_overflow(&a, &b), None);
        let both = upper.assume_proposition(bounds[1].clone());
        let (answer, sources) = collect_consulted_premises(|| {
            capture_implicit_consulted_premises(|| both.exact_signed_add_overflow(&a, &b))
        });
        assert_eq!(answer, Some(false));
        assert!(bounds.iter().all(|bound| sources.contains(bound)));
        assert_eq!(parent.exact_signed_add_overflow(&a, &b), None);
    }

    #[test]
    fn ordinary_overflow_queries_retain_legacy_sources_and_branch_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let written = OldMachineTerm::Binary {
            format,
            op: MachineBinaryOp::Add,
            left: Box::new(OldMachineTerm::Variable(Variable(983717))),
            right: Box::new(OldMachineTerm::Variable(Variable(983718))),
        };
        let operand = SharedMachineIntegerTerm::from_shared(
            format,
            KernelTermImport::default()
                .machine_arithmetic(format, &written)
                .unwrap(),
        )
        .unwrap();
        let query = query(
            format,
            Operation::Add,
            &operand,
            IntegerTerm::constant(2.into()),
        );
        let source = Proposition::condition_is(
            OldConditionTerm::Overflows {
                format,
                op: OverflowOperation::Add,
                left: Box::new(written),
                right: Box::new(OldMachineTerm::constant(2)),
            },
            false,
        );
        let parent = PureFactContext::new();
        let child = parent.clone().assume_proposition(source.clone());
        let (answer, sources) = collect_consulted_premises(|| {
            capture_implicit_consulted_premises(|| child.decide_overflow_query(&query))
        });
        assert_eq!(answer, Some(false));
        assert!(sources.contains(&source));
        assert_eq!(parent.decide_overflow_query(&query), None);
        assert!(!operand.has_boxed_operand());
    }

    #[test]
    fn shared_overflow_query_does_not_use_a_wrapped_result_bound() {
        let _session = crate::kernel::VerificationSession::enter();
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        let format = MachineIntegerType::Int32;
        let operand = SharedMachineIntegerTerm::from_shared(
            format,
            KernelTermImport::default()
                .machine_arithmetic(format, &OldMachineTerm::Variable(Variable(983720)))
                .unwrap(),
        )
        .unwrap();
        let query = query(
            format,
            Operation::Multiply,
            &operand,
            IntegerTerm::constant(2.into()),
        );
        let observed = crate::kernel::machine_integer::representation::operation_observation(
            format,
            Operation::Multiply,
            &operand,
            &SharedMachineIntegerTerm::from_shared(
                format,
                KernelTermImport::default()
                    .machine_arithmetic(format, &OldMachineTerm::constant(2))
                    .unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        let context = PureFactContext::new().assume_condition(
            OldConditionTerm::IntegerEqual(observed.into(), IntegerTerm::constant(6.into()).into()),
            true,
        );
        assert_eq!(context.decide_overflow_query(&query), None);
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }

    #[test]
    fn shared_ring_overflow_queries_use_operand_ranges_not_wrapped_results() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            let exports = crate::kernel::KernelTermExport::machine_export_count();
            let written = OldMachineTerm::Variable(Variable(983719));
            let operand = SharedMachineIntegerTerm::from_shared(
                format,
                KernelTermImport::default()
                    .machine_arithmetic(format, &written)
                    .unwrap(),
            )
            .unwrap();
            let observe = || IntegerTerm::Machine(operand.clone());
            let parent = PureFactContext::new();
            let bounded = parent
                .clone()
                .assume_condition(
                    OldConditionTerm::integer_less_equal(
                        observe(),
                        IntegerTerm::constant(10.into()),
                    ),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::integer_greater_equal(
                        observe(),
                        IntegerTerm::constant(0.into()),
                    ),
                    true,
                );
            for operation in [Operation::Add, Operation::Multiply] {
                let query = query(format, operation, &operand, IntegerTerm::constant(2.into()));
                assert_eq!(bounded.decide_overflow_query(&query), Some(false));
                assert_eq!(parent.decide_overflow_query(&query), None);
            }
            let same = query(format, Operation::Subtract, &operand, observe());
            assert_eq!(parent.decide_overflow_query(&same), Some(false));
            assert_eq!(
                crate::kernel::KernelTermExport::machine_export_count(),
                exports
            );
        }
    }
}

// An opaque retained leaf borrows the same native input used by the existing
// interval rules. Arithmetic parents remain shared and memoized by node id.
fn opaque_operand(view: MachineOperandView<'_>) -> MachineOperandView<'_> {
    match view {
        MachineOperandView::Shared(root) => root
            .machine_conversion_leaf()
            .map(MachineOperandView::Old)
            .unwrap_or(view),
        _ => view,
    }
}
