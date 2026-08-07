use super::*;

impl Assumptions {
    /// Decides a condition against this fact set, memoizing results by the
    /// fact set's content identity.
    ///
    /// A `Some` answer is evidence found in the facts and stays valid no
    /// matter how the search was pruned. A `None` computed under an ambient
    /// truncation (fuel, depth guards, cycle cuts — see
    /// [`note_search_truncation`]) is path-dependent and is not cached.
    pub(crate) fn decide(&self, condition: &ConditionTerm) -> Option<bool> {
        // Fuel is consumed before the memo so a fueled search keeps its
        // step budget: memoization makes each step cheaper, not the search
        // wider.
        if !consume_simp_reasoning_fuel() {
            return None;
        }
        // Debugging escape hatch: run every decision unmemoized to compare
        // against memoized behavior.
        if decide_memo_disabled() {
            let _decision_guard = ConditionDecisionGuard::enter(condition)?;
            return self.decide_inner(condition);
        }
        // Resolve the memo identity from an enclosing scope, or establish
        // one when this is the outermost decision. Nested decisions on other
        // fact sets (intrinsic decisions on fresh empty sets) run unmemoized.
        let scope = if inside_condition_decision() {
            None
        } else {
            Some(AssumptionsIdScope::enter(self))
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
        let truncations_before = SEARCH_TRUNCATIONS.with(Cell::get);
        let result = self.decide_inner(condition);
        if result.is_some() || SEARCH_TRUNCATIONS.with(Cell::get) == truncations_before {
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
        match condition {
            ConditionTerm::Constant(value) => Some(*value),
            _ => {
                if let Some(value) = self.exact_condition_value(condition) {
                    return Some(value);
                }
                let simplified = self.simplify_condition_under_assumptions(condition);
                if simplified != *condition {
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

    pub(in crate::kernel) fn decide_intrinsically(condition: &ConditionTerm) -> Option<bool> {
        Self::new().decide(condition)
    }

    pub(in crate::kernel) fn has_condition_fact(
        &self,
        condition: ConditionTerm,
        value: bool,
    ) -> bool {
        self.condition_facts.get(&condition) == Some(&value)
            || self.condition_facts.iter().any(|(fact, fact_value)| {
                *fact_value == value && self.condition_matches(fact, &condition)
            })
    }

    pub(in crate::kernel) fn exact_condition_value(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
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
        if left == right || self.bitvector_terms_equal_from_facts(left, right) {
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
        // execution and pinned replay.
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

    fn bitvector_constant_from_direct_equalities(&self, term: &Bitvector32Term) -> Option<u32> {
        let mut pending = vec![term.clone()];
        let mut visited = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            if let Some(value) = current.as_const() {
                return Some(value);
            }
            for (condition, value) in &self.condition_facts {
                let (ConditionTerm::Bitvector32Equal(left, right), true) = (condition, value)
                else {
                    continue;
                };
                if left.as_ref() == &current {
                    pending.push(right.as_ref().clone());
                }
                if right.as_ref() == &current {
                    pending.push(left.as_ref().clone());
                }
            }
        }
        None
    }

    pub(in crate::kernel) fn bitvector_terms_equal_from_facts(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }

        // Memoized only under an enclosing id scope; this search is called
        // from deep memory-resolution recursions where hashing the fact set
        // per call would cost more than the search itself.
        let memo_id = if decide_memo_disabled() {
            None
        } else {
            ambient_assumptions_memo_id(self)
        };
        let memo_key = memo_id.map(|memo_id| (memo_id, left.clone(), right.clone()));
        if let Some(memo_key) = &memo_key
            && let Some(hit) =
                EQUAL_FROM_FACTS_MEMO.with(|memo| memo.borrow().get(memo_key).copied())
        {
            return hit;
        }
        let result = self.bitvector_terms_equal_from_facts_uncached(left, right);
        if let Some(memo_key) = memo_key {
            EQUAL_FROM_FACTS_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DECIDE_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(memo_key, result);
            });
        }
        result
    }

    /// The equality-graph search behind [`Self::bitvector_terms_equal_from_facts`].
    /// This search is pure — it consults no fuel or depth guards — so both
    /// positive and negative results are memoizable by content identity.
    fn bitvector_terms_equal_from_facts_uncached(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let mut seen = BTreeSet::new();
        let mut stack = vec![left.clone()];
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            if equality_graph_terms_match(&term, right) {
                return true;
            }
            for (condition, value) in &self.condition_facts {
                if !*value {
                    continue;
                }
                match condition {
                    ConditionTerm::Bitvector32Equal(fact_left, fact_right) => {
                        if equality_graph_terms_match(fact_left, &term) {
                            stack.push(fact_right.as_ref().clone());
                        }
                        if equality_graph_terms_match(fact_right, &term) {
                            stack.push(fact_left.as_ref().clone());
                        }
                    }
                    ConditionTerm::PointerOffsetEqual(fact_left, fact_right) => {
                        let (Some(fact_left), Some(fact_right)) = (
                            int32_element_index_from_offset(fact_left),
                            int32_element_index_from_offset(fact_right),
                        ) else {
                            continue;
                        };
                        if equality_graph_terms_match(&fact_left, &term) {
                            stack.push(fact_right.clone());
                        }
                        if equality_graph_terms_match(&fact_right, &term) {
                            stack.push(fact_left);
                        }
                    }
                    _ => {}
                }
            }
        }

        false
    }

    pub(in crate::kernel) fn simplify_condition_under_assumptions(
        &self,
        condition: &ConditionTerm,
    ) -> ConditionTerm {
        match condition {
            ConditionTerm::Constant(value) => ConditionTerm::Constant(*value),
            ConditionTerm::Variable(variable) => ConditionTerm::Variable(*variable),
            ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                ConditionTerm::signed_less_than(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                ConditionTerm::signed_less_equal(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                ConditionTerm::signed_greater_than(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                ConditionTerm::signed_greater_equal(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32Equal(left, right) => ConditionTerm::equal(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                ConditionTerm::signed_add_overflows(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
                ConditionTerm::signed_subtract_overflows(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
                ConditionTerm::signed_multiply_overflows(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
                ConditionTerm::signed_divide_overflows(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
                ConditionTerm::signed_shift_left_overflows(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                ConditionTerm::pointer_offset_equal(left.as_ref().clone(), right.as_ref().clone())
            }
            ConditionTerm::PointerEqual(left, right) => {
                ConditionTerm::pointer_equal(left.as_ref().clone(), right.as_ref().clone())
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
            Bitvector32Term::Constant(value) => Bitvector32Term::Constant(*value),
            Bitvector32Term::Variable(variable) => Bitvector32Term::Variable(*variable),
            Bitvector32Term::Add(left, right) => Bitvector32Term::add(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::Subtract(left, right) => Bitvector32Term::subtract(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::Multiply(left, right) => Bitvector32Term::multiply(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::Divide(left, right) => Bitvector32Term::divide(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::Remainder(left, right) => Bitvector32Term::remainder(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::ShiftLeft(left, right) => Bitvector32Term::shift_left(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::ArithmeticShiftRight(left, right) => {
                Bitvector32Term::arithmetic_shift_right(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            Bitvector32Term::BitwiseAnd(left, right) => Bitvector32Term::bitwise_and(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::BitwiseOr(left, right) => Bitvector32Term::bitwise_or(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::BitwiseXor(left, right) => Bitvector32Term::bitwise_xor(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::BitwiseNot(value) => {
                Bitvector32Term::bitwise_not(self.simplify_bitvector_under_assumptions(value))
            }
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
            Bitvector32Term::MemoryLoad(memory, pointer) => {
                Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone())
            }
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
        for (condition, value) in &self.condition_facts {
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

        matches!((range.lower, range.upper), (Some(lower), Some(upper)) if lower == upper && lower == constant)
    }

    pub(in crate::kernel) fn signed_constant_known_equal(
        &self,
        term: &Bitvector32Term,
    ) -> Option<i64> {
        if let Some(value) = signed_bitvector_constant(term) {
            return Some(value);
        }

        for (condition, value) in &self.condition_facts {
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

    fn signed_constant_after_equality_normalization(&self, term: &Bitvector32Term) -> Option<i64> {
        // The walk re-resolves the same subterms across goals and claims;
        // memoize by fact-set content identity exactly like `decide`.
        if decide_memo_disabled() {
            return self.signed_constant_after_equality_normalization_unmemoized(term);
        }
        let _scope = AssumptionsIdScope::enter(self);
        let key = (_scope.id, term.clone());
        if let Some(hit) = CONSTANT_NORMALIZATION_MEMO.with(|memo| memo.borrow().get(&key).copied())
        {
            return hit;
        }
        let truncations_before = SEARCH_TRUNCATIONS.with(Cell::get);
        let result = self.signed_constant_after_equality_normalization_unmemoized(term);
        if result.is_some() || SEARCH_TRUNCATIONS.with(Cell::get) == truncations_before {
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
        let mut remaining = CONSTANT_NORMALIZATION_SEARCH_LIMIT;
        match self.signed_constant_after_equality_normalization_inner(
            term,
            &mut BTreeSet::new(),
            &mut remaining,
        ) {
            SignedConstantResolution::Known(value) => Some(value),
            SignedConstantResolution::Unknown | SignedConstantResolution::Ambiguous => None,
        }
    }

    fn signed_constant_after_equality_normalization_inner(
        &self,
        term: &Bitvector32Term,
        resolving: &mut BTreeSet<Bitvector32Term>,
        remaining: &mut usize,
    ) -> SignedConstantResolution {
        let Some(next) = remaining.checked_sub(1) else {
            note_search_truncation();
            return SignedConstantResolution::Unknown;
        };
        *remaining = next;
        if let Some(value) = signed_bitvector_constant(term) {
            return SignedConstantResolution::Known(value);
        }
        // Subterms recur across fact paths within one walk; a memoized Known
        // is fact evidence and stays valid however the search was pruned, so
        // it may be reused at any depth (Unknown under an active `resolving`
        // cycle cut is path-dependent and is only cached by the outer entry
        // point).
        let memo_id = ambient_assumptions_memo_id(self);
        if let Some(memo_id) = memo_id
            && let Some(Some(known)) = CONSTANT_NORMALIZATION_MEMO
                .with(|memo| memo.borrow().get(&(memo_id, term.clone())).copied())
        {
            return SignedConstantResolution::Known(known);
        }
        if !resolving.insert(term.clone()) {
            return SignedConstantResolution::Unknown;
        }

        let mut result = match term {
            Bitvector32Term::Add(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::add,
            ),
            Bitvector32Term::Subtract(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::subtract,
            ),
            Bitvector32Term::Multiply(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::multiply,
            ),
            Bitvector32Term::Divide(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::divide,
            ),
            Bitvector32Term::Remainder(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::remainder,
            ),
            Bitvector32Term::ShiftLeft(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::shift_left,
            ),
            Bitvector32Term::ArithmeticShiftRight(left, right) => self
                .signed_binary_constant_known_equal(
                    left,
                    right,
                    resolving,
                    remaining,
                    Bitvector32Term::arithmetic_shift_right,
                ),
            Bitvector32Term::BitwiseAnd(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::bitwise_and,
            ),
            Bitvector32Term::BitwiseOr(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::bitwise_or,
            ),
            Bitvector32Term::BitwiseXor(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                remaining,
                Bitvector32Term::bitwise_xor,
            ),
            Bitvector32Term::BitwiseNot(value) => self
                .signed_constant_after_equality_normalization_inner(value, resolving, remaining)
                .map(|value| {
                    Bitvector32Term::bitwise_not(Bitvector32Term::Constant(value as i32 as u32))
                }),
            Bitvector32Term::If {
                condition,
                then_term,
                else_term,
            } => match self.decide(condition) {
                Some(condition) => self.signed_constant_after_equality_normalization_inner(
                    if condition { then_term } else { else_term },
                    resolving,
                    remaining,
                ),
                None => SignedConstantResolution::Unknown,
            },
            _ => SignedConstantResolution::Unknown,
        };

        // Deep equality (with snapshot bridging) is only worth attempting on
        // candidates that could plausibly denote this term: two loads must
        // read the same block through offsets built from the same number of
        // atoms, and a load never equals a non-load term through this walk
        // except via another fact that mentions the load itself. Without the
        // gate the walk pays a bridging search against every fact at every
        // recursion level.
        let plausibly_equal = |candidate: &Bitvector32Term| match (term, candidate) {
            (
                Bitvector32Term::MemoryLoad(_, term_pointer),
                Bitvector32Term::MemoryLoad(_, candidate_pointer),
            ) => pointers_equal_ignoring_memories(term_pointer, candidate_pointer),
            (Bitvector32Term::MemoryLoad(_, _), _) | (_, Bitvector32Term::MemoryLoad(_, _)) => {
                false
            }
            _ => true,
        };
        for (condition, value) in &self.condition_facts {
            let (ConditionTerm::Bitvector32Equal(left, right), true) = (condition, value) else {
                continue;
            };
            if plausibly_equal(left) && self.bitvector_terms_proven_equal(term, left) {
                result = result.merge(self.signed_constant_after_equality_normalization_inner(
                    right, resolving, remaining,
                ));
            }
            if plausibly_equal(right) && self.bitvector_terms_proven_equal(term, right) {
                result = result.merge(self.signed_constant_after_equality_normalization_inner(
                    left, resolving, remaining,
                ));
            }
        }

        resolving.remove(term);
        if let SignedConstantResolution::Known(known) = result
            && let Some(memo_id) = memo_id
        {
            CONSTANT_NORMALIZATION_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DECIDE_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert((memo_id, term.clone()), Some(known));
            });
        }
        result
    }

    fn signed_binary_constant_known_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        resolving: &mut BTreeSet<Bitvector32Term>,
        remaining: &mut usize,
        operation: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
    ) -> SignedConstantResolution {
        let left =
            self.signed_constant_after_equality_normalization_inner(left, resolving, remaining);
        let right =
            self.signed_constant_after_equality_normalization_inner(right, resolving, remaining);
        match (left, right) {
            (SignedConstantResolution::Ambiguous, _) | (_, SignedConstantResolution::Ambiguous) => {
                SignedConstantResolution::Ambiguous
            }
            (SignedConstantResolution::Known(left), SignedConstantResolution::Known(right)) => {
                SignedConstantResolution::from_term(operation(
                    Bitvector32Term::Constant(left as i32 as u32),
                    Bitvector32Term::Constant(right as i32 as u32),
                ))
            }
            _ => SignedConstantResolution::Unknown,
        }
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
                        let left_index = int32_element_index_from_offset(left);
                        let right_index = int32_element_index_from_offset(right);
                        match (left_index, right_index) {
                            (Some(left), Some(right)) => {
                                self.decide(&ConditionTerm::equal(left, right))
                            }
                            _ => {
                                let left_bytes = byte_offset_from_pointer_offset(left);
                                let right_bytes = byte_offset_from_pointer_offset(right);
                                match (left_bytes, right_bytes) {
                                    (Some(left), Some(right)) => {
                                        self.decide(&ConditionTerm::equal(left, right))
                                    }
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
            |pointer: &Pointer| crate::kernel::api::canonicalize_pointer_loads(pointer, 0);
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
        let mut seen = BTreeSet::from([left.clone()]);
        let mut frontier = vec![left.clone()];
        while let Some(current) = frontier.pop() {
            for (condition, value) in &self.condition_facts {
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
    /// checks from exact facts alone.
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

    pub(super) fn has_exact_order_path(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let order_facts = self.condition_order_facts();
        // Two spellings of one load at different snapshots connect along
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
            for (edge_left, edge_right, edge_strict) in &order_facts {
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

    pub(super) fn has_order_path_for_memory_resolution(
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
            for (edge_left, edge_right, edge_strict) in &order_facts {
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
            for (condition, value) in &self.condition_facts {
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

    pub(crate) fn decide_condition_for_simp(&self, condition: &ConditionTerm) -> Option<bool> {
        if let Some(value) = self.exact_condition_value(condition) {
            return Some(value);
        }

        match condition {
            ConditionTerm::Constant(value) => Some(*value),
            ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerEqual(left, right)
                if self.has_pointer_equality_path(left, right) =>
            {
                Some(true)
            }
            ConditionTerm::PointerEqual(left, right) if left.blocks_proven_distinct(right) => {
                Some(false)
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                if pointer_offsets_proven_equal_for_memory_resolution(left, right, self) {
                    Some(true)
                } else {
                    match (left.as_ref().as_const(), right.as_ref().as_const()) {
                        (Some(left), Some(right)) => Some(left == right),
                        _ => None,
                    }
                }
            }
            ConditionTerm::Bitvector32Equal(left, right) => {
                if bitvector_terms_proven_equal_for_memory_resolution(left, right, self)
                    || self.proves_condition_from_facts_for_simp(condition, true)
                {
                    Some(true)
                } else if bitvector_same_base_nonzero_const_offset(left, right) {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
                if left.as_ref().add_const_base(1).is_some_and(|base| {
                    self.exact_condition_value(&ConditionTerm::signed_less_than(
                        base,
                        right.as_ref().clone(),
                    )) == Some(true)
                }) =>
            {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right)
                if self.exact_condition_value(&ConditionTerm::signed_less_than(
                    left.as_ref().clone(),
                    Bitvector32Term::Add(
                        Box::new(right.as_ref().clone()),
                        Box::new(Bitvector32Term::Constant(1)),
                    ),
                )) == Some(true)
                    && self.has_exact_bitvector_inequality_after_cancellation(left, right) =>
            {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right)
                if self.positive_offset_is_proven_above_for_simp(left, right) =>
            {
                Some(true)
            }
            _ => {
                if self.proves_condition_from_facts_for_simp(condition, true) {
                    return Some(true);
                }
                if self.proves_condition_from_facts_for_simp(condition, false) {
                    return Some(false);
                }
                // This stronger normalization is tactic-local. Keep its atomic
                // checks structural: calling the general condition solver here
                // can recurse through fact transport and memory alias solving.
                if let Some((left, right, strict)) = condition_as_order_fact(condition, true)
                    && self.has_order_path_for_simp(&left, &right, strict)
                {
                    return Some(true);
                }
                if let Some((left, right, strict)) = condition_as_order_fact(condition, false)
                    && self.has_order_path_for_simp(&left, &right, strict)
                {
                    return Some(false);
                }
                if condition_as_order_fact(condition, true).is_some() {
                    Self::decide_intrinsically(condition)
                } else {
                    self.decide(condition)
                }
            }
        }
    }

    fn has_exact_bitvector_inequality_after_cancellation(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.exact_condition_value(&ConditionTerm::equal(left.clone(), right.clone()))
            == Some(false)
            || self.condition_facts.iter().any(|(condition, value)| {
                if *value {
                    return false;
                }
                let ConditionTerm::Bitvector32Equal(fact_left, fact_right) = condition else {
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

    fn decide_condition_for_simp_without_prop_facts(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        if let Some(value) = self.exact_condition_value(condition) {
            return Some(value);
        }
        if let ConditionTerm::Constant(value) = condition {
            return Some(*value);
        }
        if let ConditionTerm::Bitvector32SignedLessThan(left, right) = condition
            && self.exact_condition_value(&ConditionTerm::signed_less_than(
                left.as_ref().clone(),
                Bitvector32Term::Add(
                    Box::new(right.as_ref().clone()),
                    Box::new(Bitvector32Term::Constant(1)),
                ),
            )) == Some(true)
            && self.has_exact_bitvector_inequality_after_cancellation(left, right)
        {
            return Some(true);
        }
        if let Some((left, right, strict)) = condition_as_order_fact(condition, true)
            && self.has_order_path_for_simp(&left, &right, strict)
        {
            return Some(true);
        }
        if let Some((left, right, strict)) = condition_as_order_fact(condition, false)
            && self.has_order_path_for_simp(&left, &right, strict)
        {
            return Some(false);
        }
        Self::decide_intrinsically(condition)
    }

    fn proves_condition_from_facts_for_simp(&self, condition: &ConditionTerm, value: bool) -> bool {
        let Some(_depth) = SimpFactReasoningDepthGuard::enter() else {
            return false;
        };
        self.condition_facts.iter().any(|(fact, fact_value)| {
            *fact_value == value && self.condition_matches_for_simp(fact, condition)
        }) || self.prop_facts.iter().any(|proposition| {
            self.proposition_proves_condition_for_simp(proposition, condition, value)
        })
    }

    pub(in crate::kernel) fn has_matching_condition_fact_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        self.condition_facts.iter().any(|(fact, fact_value)| {
            *fact_value == value && self.condition_matches_for_simp(fact, condition)
        })
    }

    pub(in crate::kernel) fn has_anchored_bitvector_equality_fact_for_memory_resolution(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.condition_facts.iter().any(|(fact, value)| {
            let (ConditionTerm::Bitvector32Equal(fact_left, fact_right), true) = (fact, value)
            else {
                return false;
            };
            let anchored = fact_left.as_ref() == left
                || fact_left.as_ref() == right
                || fact_right.as_ref() == left
                || fact_right.as_ref() == right;
            anchored
                && self.condition_matches_for_simp(
                    fact,
                    &ConditionTerm::equal(left.clone(), right.clone()),
                )
        })
    }

    fn proposition_proves_condition_for_simp(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        match proposition {
            Proposition::ConditionIs(fact, fact_value) => {
                *fact_value == value && self.condition_matches_for_simp(fact, condition)
            }
            Proposition::And(left, right) => {
                self.proposition_proves_condition_for_simp(left, condition, value)
                    || self.proposition_proves_condition_for_simp(right, condition, value)
            }
            Proposition::Implies(left, right) => {
                // Reject implications whose conclusion cannot establish the
                // target before proving their (potentially expensive)
                // antecedent against the whole context.
                self.proposition_proves_condition_for_simp(right, condition, value)
                    && self.proves_proposition_for_simp_without_search(left)
            }
            Proposition::ForAll { body, .. } => {
                self.proposition_proves_condition_for_simp(body, condition, value)
                    || self
                        .forall_instantiations_for_condition(proposition, condition)
                        .iter()
                        .any(|instance| {
                            self.proposition_proves_condition_for_simp(instance, condition, value)
                        })
            }
            _ => false,
        }
    }

    fn proves_proposition_for_simp_without_search(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide_condition_for_simp_without_prop_facts(condition) == Some(*value)
            }
            Proposition::And(left, right) => {
                self.proves_proposition_for_simp_without_search(left)
                    && self.proves_proposition_for_simp_without_search(right)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide_condition_for_simp_without_prop_facts(condition) == Some(!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            _ => self.proves_exact(proposition),
        }
    }

    fn condition_matches_for_simp(&self, fact: &ConditionTerm, target: &ConditionTerm) -> bool {
        if fact == target {
            return true;
        }
        match (fact, target) {
            (
                ConditionTerm::Bitvector32Equal(fact_left, fact_right),
                ConditionTerm::Bitvector32Equal(target_left, target_right),
            ) => {
                bitvector_terms_proven_equal_for_memory_resolution(fact_left, target_left, self)
                    && bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        target_right,
                        self,
                    )
                    || bitvector_terms_proven_equal_for_memory_resolution(
                        fact_left,
                        target_right,
                        self,
                    ) && bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        target_left,
                        self,
                    )
            }
            (
                ConditionTerm::PointerOffsetEqual(fact_left, fact_right),
                ConditionTerm::PointerOffsetEqual(target_left, target_right),
            ) => {
                pointer_offsets_proven_equal_for_memory_resolution(fact_left, target_left, self)
                    && pointer_offsets_proven_equal_for_memory_resolution(
                        fact_right,
                        target_right,
                        self,
                    )
                    || pointer_offsets_proven_equal_for_memory_resolution(
                        fact_left,
                        target_right,
                        self,
                    ) && pointer_offsets_proven_equal_for_memory_resolution(
                        fact_right,
                        target_left,
                        self,
                    )
            }
            (
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterEqual(target_left, target_right),
            ) => {
                bitvector_terms_proven_equal_for_memory_resolution(fact_left, target_left, self)
                    && bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        target_right,
                        self,
                    )
            }
            (
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterEqual(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            ) => {
                bitvector_terms_proven_equal_for_memory_resolution(fact_left, target_right, self)
                    && bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        target_left,
                        self,
                    )
            }
            _ => false,
        }
    }

    fn has_order_path_for_simp(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let mut order_facts = self.condition_order_facts();
        self.collect_quantified_order_facts_for_condition(
            &ConditionTerm::signed_less_than(left.clone(), right.clone()),
            &mut order_facts,
        );
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            if let Some(connection_strict) = self.order_path_connection_for_simp(&current, right)
                && (!require_strict || strict_so_far || connection_strict)
            {
                return true;
            }
            for (edge_left, edge_right, edge_strict) in &order_facts {
                if let Some(connection_strict) =
                    self.order_path_connection_for_simp(&current, edge_left)
                {
                    stack.push((
                        edge_right.clone(),
                        strict_so_far || connection_strict || *edge_strict,
                    ));
                }
            }
        }
        false
    }

    fn positive_offset_is_proven_above_for_simp(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        let Some((term_base, addend)) = term.add_const_parts() else {
            return false;
        };
        if !self.bitvector_terms_equal_for_simp(&term_base, base)
            || signed_u32_constant(addend).is_none_or(|value| value <= 0)
        {
            return false;
        }
        // A strict upper bound by any int32 value proves that `base` is below
        // INT_MAX. Therefore adding one cannot wrap. Keep this simp rule
        // syntactic so certificate selection cannot recurse into memory or
        // alias resolution.
        addend == 1
            && self.condition_facts.iter().any(|(condition, value)| {
                matches!(
                    (condition, value),
                    (
                        ConditionTerm::Bitvector32SignedLessThan(left, _),
                        true
                    ) if self.bitvector_terms_equal_for_simp(left, base)
                ) || matches!(
                    (condition, value),
                    (
                        ConditionTerm::Bitvector32SignedGreaterThan(_, right),
                        true
                    ) if self.bitvector_terms_equal_for_simp(right, base)
                )
            })
    }

    /// Resolves both sides to known constants through equality facts (with
    /// per-load snapshot bridging) and compares them. Deterministic and
    /// bounded: the resolution walk carries its own visited set and consults
    /// no fuel, so certification may use it.
    pub(in crate::kernel) fn constants_known_equal_after_normalization(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some(left) = self.signed_constant_after_equality_normalization(left) else {
            return false;
        };
        let Some(right) = self.signed_constant_after_equality_normalization(right) else {
            return false;
        };
        left == right
    }

    /// The unique constant this term resolves to through equality facts
    /// (with per-load snapshot bridging), if any. Bounded and fuel-free.
    pub(in crate::kernel) fn known_signed_constant_after_normalization(
        &self,
        term: &Bitvector32Term,
    ) -> Option<i64> {
        self.signed_constant_after_equality_normalization(term)
    }

    /// Decides a signed comparison whose sides both resolve to known
    /// constants through equality facts (with per-load snapshot bridging).
    /// Bounded and fuel-free, so certification may use it.
    pub(in crate::kernel) fn signed_comparison_by_constant_normalization(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        let (left, right, compare): (_, _, fn(i64, i64) -> bool) = match condition {
            ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                (left, right, |left, right| left < right)
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                (left, right, |left, right| left <= right)
            }
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                (left, right, |left, right| left > right)
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                (left, right, |left, right| left >= right)
            }
            _ => return None,
        };
        let left = self.signed_constant_after_equality_normalization(left)?;
        let right = self.signed_constant_after_equality_normalization(right)?;
        Some(compare(left, right))
    }

    fn order_path_connection_for_simp(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        if self.bitvector_terms_equal_for_simp(left, right) {
            return Some(false);
        }
        if self.positive_offset_is_proven_above_for_simp(left, right) {
            return Some(true);
        }
        let left = self.signed_constant_after_equality_normalization(left)?;
        let right = self.signed_constant_after_equality_normalization(right)?;
        (left <= right).then_some(left < right)
    }

    fn bitvector_terms_equal_for_simp(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if self.bitvector_terms_equal_for_transport(left, right) {
            return true;
        }

        self.condition_facts.iter().any(|(condition, value)| {
            let (ConditionTerm::Bitvector32Equal(fact_left, fact_right), true) = (condition, value)
            else {
                return false;
            };
            self.bitvector_terms_equal_for_transport(left, fact_left)
                && self.bitvector_terms_equal_for_transport(right, fact_right)
                || self.bitvector_terms_equal_for_transport(left, fact_right)
                    && self.bitvector_terms_equal_for_transport(right, fact_left)
        })
    }

    pub(in crate::kernel) fn condition_order_facts(
        &self,
    ) -> Vec<(Bitvector32Term, Bitvector32Term, bool)> {
        let mut facts = Vec::new();
        for (condition, value) in &self.condition_facts {
            if crate::instrumentation::deadline_exceeded() {
                break;
            }
            if let Some(fact) = condition_as_order_fact(condition, *value) {
                facts.push(fact);
            }
        }
        facts
    }

    pub(in crate::kernel) fn collect_derived_order_facts(
        &self,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        for proposition in &self.prop_facts {
            self.collect_derived_order_facts_from_proposition(proposition, order_facts);
        }
    }

    pub(in crate::kernel) fn collect_derived_order_facts_from_proposition(
        &self,
        proposition: &Proposition,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                if let Some(order_fact) = condition_as_order_fact(condition, *value) {
                    order_facts.push(order_fact);
                }
            }
            Proposition::And(left, right) => {
                self.collect_derived_order_facts_from_proposition(left, order_facts);
                self.collect_derived_order_facts_from_proposition(right, order_facts);
            }
            Proposition::Implies(left, right) if self.proves_without_prop_facts(left) => {
                self.collect_derived_order_facts_from_proposition(right, order_facts);
            }
            Proposition::ForAll { .. } => {
                self.collect_finite_forall_order_facts(proposition, order_facts);
            }
            _ => {}
        }
    }

    pub(in crate::kernel) fn collect_finite_forall_order_facts(
        &self,
        proposition: &Proposition,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        let mut variables = Vec::new();
        let body = collect_forall_chain(proposition, &mut variables);
        if variables.is_empty() {
            return;
        }
        let Some(ranges) = finite_forall_ranges(&variables, body) else {
            return;
        };
        let Some(instantiation_count) = ranges.iter().try_fold(1usize, |count, range| {
            let width = usize::try_from(range.upper - range.lower + 1).ok()?;
            count.checked_mul(width)
        }) else {
            return;
        };
        if instantiation_count > FINITE_FORALL_INSTANTIATION_LIMIT {
            return;
        }

        let mut values = Vec::with_capacity(variables.len());
        self.collect_finite_forall_order_fact_instantiations(
            body,
            &variables,
            &ranges,
            &mut values,
            order_facts,
        );
    }

    pub(in crate::kernel) fn collect_finite_forall_order_fact_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for (variable, value) in variables.iter().zip(values.iter()) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &signed_i64_bitvector_constant(*value),
                );
            }
            self.collect_derived_order_facts_from_proposition(&instantiated, order_facts);
            return;
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            self.collect_finite_forall_order_fact_instantiations(
                body,
                variables,
                ranges,
                values,
                order_facts,
            );
            values.pop();
        }
    }

    pub(in crate::kernel) fn has_upper_bound_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedLessThan(fact_left, upper), true)
                    if self.bitvector_terms_equal_for_transport(fact_left, left) =>
                {
                    self.decide(&ConditionTerm::signed_less_equal(
                        upper.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                _ => false,
            })
    }

    pub(in crate::kernel) fn has_upper_bound_at_or_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedLessEqual(fact_left, upper), true)
                    if self.bitvector_terms_equal_for_transport(fact_left, left) =>
                {
                    self.decide(&ConditionTerm::signed_less_equal(
                        upper.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                (ConditionTerm::Bitvector32SignedGreaterEqual(upper, fact_left), true)
                    if self.bitvector_terms_equal_for_transport(fact_left, left) =>
                {
                    self.decide(&ConditionTerm::signed_less_equal(
                        upper.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                _ => false,
            })
    }

    pub(in crate::kernel) fn has_successor_upper_bound_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedLessThan(fact_left, upper), true)
                    if fact_left.as_ref() == left
                        && upper
                            .as_ref()
                            .add_const_base(1)
                            .is_some_and(|base| base == *right) =>
                {
                    self.has_condition_fact(
                        ConditionTerm::equal(left.clone(), right.clone()),
                        false,
                    )
                }
                _ => false,
            })
    }

    pub(in crate::kernel) fn has_add_const_upper_bound_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        if self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) != Some(false)
        {
            return false;
        }

        self.condition_facts
            .iter()
            .filter_map(|(condition, value)| condition_as_order_fact(condition, *value))
            .any(|(fact_left, upper, strict)| {
                if fact_left != base {
                    return false;
                }
                let Some(upper) = signed_const_add(&upper, addend) else {
                    return false;
                };
                if strict {
                    self.decide(&ConditionTerm::signed_less_equal(upper, right.clone()))
                        == Some(true)
                } else {
                    self.decide(&ConditionTerm::signed_less_than(upper, right.clone()))
                        == Some(true)
                }
            })
    }

    pub(in crate::kernel) fn has_add_const_upper_bound_at_or_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        if self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) != Some(false)
        {
            return false;
        }

        self.condition_facts
            .iter()
            .filter_map(|(condition, value)| condition_as_order_fact(condition, *value))
            .any(|(fact_left, upper, _strict)| {
                if fact_left != base {
                    return false;
                }
                let Some(upper) = signed_const_add(&upper, addend) else {
                    return false;
                };
                self.decide(&ConditionTerm::signed_less_equal(upper, right.clone())) == Some(true)
            })
    }

    pub(in crate::kernel) fn subtract_same_const_order_fact(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        let Some((left_base, left_const)) = left.subtract_const_parts() else {
            return false;
        };
        let Some((right_base, right_const)) = right.subtract_const_parts() else {
            return false;
        };
        if left_const != right_const {
            return false;
        }
        // `base - const` wraps; an order between the bases only carries to
        // the subtracted terms when neither subtraction signed underflows
        // (otherwise `a < b` would prove `a - 1 < b - 1`, false at
        // a = INT_MIN, b = INT_MIN + 1).
        if self.decide(&ConditionTerm::signed_subtract_overflows(
            left_base.clone(),
            Bitvector32Term::Constant(left_const),
        )) != Some(false)
            || self.decide(&ConditionTerm::signed_subtract_overflows(
                right_base.clone(),
                Bitvector32Term::Constant(right_const),
            )) != Some(false)
        {
            return false;
        }

        if strict {
            self.has_condition_fact(
                ConditionTerm::signed_less_than(left_base.clone(), right_base.clone()),
                true,
            ) || self.has_condition_fact(
                ConditionTerm::signed_greater_than(right_base, left_base),
                true,
            )
        } else {
            self.has_condition_fact(
                ConditionTerm::signed_less_equal(left_base.clone(), right_base.clone()),
                true,
            ) || self.has_condition_fact(
                ConditionTerm::signed_greater_equal(right_base, left_base),
                true,
            )
        }
    }

    pub(in crate::kernel) fn has_lower_bound_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let bound_is_above = |lower: &Bitvector32Term| {
            if !self.should_defer_non_exact_condition_reasoning() {
                return self.decide(&ConditionTerm::signed_greater_than(
                    lower.clone(),
                    right.clone(),
                )) == Some(true);
            }
            match (
                signed_bitvector_constant(lower),
                signed_bitvector_constant(right),
            ) {
                (Some(lower), Some(right)) => lower > right,
                _ => {
                    self.exact_condition_value(&ConditionTerm::signed_greater_than(
                        lower.clone(),
                        right.clone(),
                    )) == Some(true)
                        || self.has_order_path(right, lower, true)
                }
            }
        };
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, lower), true)
                    if self.bitvector_terms_equal_for_transport(fact_left, left) =>
                {
                    bound_is_above(lower)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if self.bitvector_terms_equal_for_transport(fact_left, left) =>
                {
                    bound_is_above(lower)
                }
                _ => false,
            })
    }

    pub(in crate::kernel) fn has_lower_bound_at_or_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, lower), true)
                    if self.bitvector_terms_equal_for_transport(fact_left, left) =>
                {
                    self.decide(&ConditionTerm::signed_greater_equal(
                        lower.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if self.bitvector_terms_equal_for_transport(fact_left, left) =>
                {
                    self.decide(&ConditionTerm::signed_greater_equal(
                        lower.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                _ => false,
            })
    }

    pub(in crate::kernel) fn has_add_const_lower_bound_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        // `base + addend` wraps in two's complement, so a bound on `base`
        // only carries to `base + addend` when that sum does not signed
        // overflow. Without this guard `x >= 0` would wrongly prove
        // `x + 1 > 0` (false at x = INT_MAX). See positive_offset_is_proven_above.
        if self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) != Some(false)
        {
            return false;
        }
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, lower), true)
                    if bitvector_terms_equal_after_exact_materialization(fact_left, &base) =>
                {
                    let Some(lower) = signed_const_add(lower, addend) else {
                        return false;
                    };
                    self.decide(&ConditionTerm::signed_greater_than(lower, right.clone()))
                        == Some(true)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if bitvector_terms_equal_after_exact_materialization(fact_left, &base) =>
                {
                    let Some(lower) = signed_const_add(lower, addend) else {
                        return false;
                    };
                    self.decide(&ConditionTerm::signed_greater_than(lower, right.clone()))
                        == Some(true)
                }
                _ => false,
            })
    }

    pub(in crate::kernel) fn has_add_const_lower_bound_at_or_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        // `base + addend` wraps; only carry the bound when it does not
        // signed overflow (otherwise `x >= 0` would prove `x + 1 >= 1`,
        // false at x = INT_MAX).
        if self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) != Some(false)
        {
            return false;
        }
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, lower), true)
                    if bitvector_terms_equal_after_exact_materialization(fact_left, &base) =>
                {
                    let Some(lower) = signed_const_add(lower, addend) else {
                        return false;
                    };
                    self.decide(&ConditionTerm::signed_greater_equal(lower, right.clone()))
                        == Some(true)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if bitvector_terms_equal_after_exact_materialization(fact_left, &base) =>
                {
                    let Some(lower) = signed_const_add(lower, addend) else {
                        return false;
                    };
                    self.decide(&ConditionTerm::signed_greater_equal(lower, right.clone()))
                        == Some(true)
                }
                _ => false,
            })
    }

    pub(in crate::kernel) fn positive_offset_is_proven_above(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        let Some((term_base, addend)) = term.add_const_parts() else {
            return false;
        };
        if &term_base != base || signed_u32_constant(addend).is_none_or(|value| value <= 0) {
            return false;
        }
        self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) == Some(false)
    }

    pub(in crate::kernel) fn positive_subtraction_is_proven_below(
        &self,
        term: &Bitvector32Term,
        base: &Bitvector32Term,
    ) -> bool {
        let Some((term_base, subtrahend)) = term.subtract_const_parts() else {
            return false;
        };
        if &term_base != base || signed_u32_constant(subtrahend).is_none_or(|value| value <= 0) {
            return false;
        }
        self.decide(&ConditionTerm::signed_subtract_overflows(
            base.clone(),
            Bitvector32Term::Constant(subtrahend),
        )) == Some(false)
    }

    pub(in crate::kernel) fn nonnegative_offset_is_proven_at_or_above(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        let Some((term_base, addend)) = term.add_const_parts() else {
            return false;
        };
        if &term_base != base || signed_u32_constant(addend).is_none_or(|value| value < 0) {
            return false;
        }
        self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) == Some(false)
    }

    fn is_bounded_by_base_before_nonnegative_offset(
        &self,
        lower: &Bitvector32Term,
        offset_term: &Bitvector32Term,
    ) -> bool {
        let Some((base, _)) = offset_term.add_const_parts() else {
            return false;
        };
        self.exact_condition_value(&ConditionTerm::signed_less_equal(
            lower.clone(),
            base.clone(),
        )) == Some(true)
            && self.nonnegative_offset_is_proven_at_or_above(&base, offset_term)
    }

    /// Decides whether two conditions are two spellings of one fact that
    /// differ only in the memory snapshots their load atoms carry.
    ///
    /// Sound because it is exact everywhere except at load atoms, and a pair
    /// of load atoms is accepted only when `memory_loads_proven_equal`
    /// proves the two loads denote the same value under these assumptions —
    /// which for differing snapshots means proving the snapshots agree at the
    /// loaded pointer. Structurally different conditions never match.
    pub fn conditions_equal_modulo_proven_snapshots(
        &self,
        left: &ConditionTerm,
        right: &ConditionTerm,
    ) -> bool {
        conditions_equal_with_load_atoms(left, right, &|left, right| {
            left == right || self.memory_loads_proven_equal(left, right)
        })
    }

    pub(crate) fn proves_condition_exact_or_snapshot(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        self.condition_facts.iter().any(|(fact, fact_value)| {
            *fact_value == value
                && (fact == condition
                    || conditions_equal_ignoring_memories(fact, condition)
                        && self.conditions_equal_modulo_proven_snapshots(fact, condition))
        })
    }

    pub(in crate::kernel) fn memory_loads_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some(_depth_guard) = MemoryLoadEqualityDepthGuard::enter() else {
            return false;
        };
        if memory_load_terms_equal_for_fact_transport(left, right, self) {
            return true;
        }
        if let Some(left) = self.resolve_memory_load_term(left) {
            return self.bitvector_terms_proven_equal(&left, right);
        }
        if let Some(right) = self.resolve_memory_load_term(right) {
            return self.bitvector_terms_proven_equal(left, &right);
        }

        let (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) = (left, right)
        else {
            return false;
        };
        if !pointers_proven_equal(left_pointer, right_pointer, self) {
            return false;
        }
        if memories_match_for_pointer_load(left_memory, right_memory, left_pointer) {
            return true;
        }
        // The DAG answers from recorded edges before either snapshot
        // comparison below, and long before the two `prop_facts` scans that
        // reconstruct the same write history from effect summaries.
        if crate::kernel::api::loads_equal_along_memory_derivations_at(
            left_memory,
            right_memory,
            left_pointer,
            self,
        ) {
            return true;
        }
        if memories_match_for_pointer_load_under_assumptions(
            left_memory,
            right_memory,
            left_pointer,
            self,
        ) {
            return true;
        }

        false
    }

    pub(in crate::kernel) fn memory_snapshots_directly_proven_equal_for_memory_resolution(
        &self,
        left: &CMemory,
        right: &CMemory,
        pointer: &Pointer,
    ) -> bool {
        self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryMutatesOnly {
                before,
                after,
                pointers,
            } => {
                let matches = memories_match_for_pointer_load(before, left, pointer)
                    && memories_match_for_pointer_load(after, right, pointer)
                    || memories_match_for_pointer_load(before, right, pointer)
                        && memories_match_for_pointer_load(after, left, pointer);
                matches
                    && pointers.iter().all(|write| {
                        pointers_proven_distinct_for_memory_resolution(write, pointer, self)
                    })
            }
            Proposition::CMemoryEffectSummary {
                before,
                after,
                mutable_ranges,
            } => {
                let endpoint_matches = |expected: &CMemory, actual: &CMemory| {
                    memory_matches_effect_summary_endpoint(expected, actual, pointer)
                        || memories_match_for_pointer_load_under_assumptions(
                            expected, actual, pointer, self,
                        )
                };
                let matches = endpoint_matches(before, left) && endpoint_matches(after, right)
                    || endpoint_matches(before, right) && endpoint_matches(after, left);
                matches && self.ranges_directly_disjoint_from_pointer(mutable_ranges, pointer)
            }
            Proposition::CHeapLifetimeRetired {
                before,
                after,
                allocation_base,
                bytes,
            } => {
                let endpoint_matches = |expected: &CMemory, actual: &CMemory| {
                    memory_matches_effect_summary_endpoint(expected, actual, pointer)
                        || memories_match_for_pointer_load_under_assumptions(
                            expected, actual, pointer, self,
                        )
                };
                let matches = endpoint_matches(before, left) && endpoint_matches(after, right)
                    || endpoint_matches(before, right) && endpoint_matches(after, left);
                matches
                    && crate::kernel::api::heap_allocation_proven_separate_from_pointer(
                        allocation_base,
                        bytes,
                        pointer,
                        self,
                    )
            }
            _ => false,
        })
    }

    pub(in crate::kernel) fn resolve_memory_load_term(
        &self,
        term: &Bitvector32Term,
    ) -> Option<Bitvector32Term> {
        let Bitvector32Term::MemoryLoad(memory, pointer) = term else {
            return None;
        };
        let CValue::Int32(value) = self.resolve_memory_load_value(memory, pointer)? else {
            return None;
        };
        (&value != term).then_some(value)
    }

    pub(in crate::kernel) fn resolve_memory_load_value(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
    ) -> Option<CValue> {
        if let Some(value) = memory.known_value(pointer) {
            return Some(value);
        }

        let mut unresolved_alias = false;
        for (cell_pointer, value) in &memory.cells {
            if pointers_proven_distinct_for_memory_resolution(cell_pointer, pointer, self) {
                continue;
            }
            if pointers_proven_equal_for_memory_resolution(cell_pointer, pointer, self) {
                return Some(value.clone());
            }
            unresolved_alias = true;
        }

        if unresolved_alias {
            return None;
        }

        memory
            .is_loadable_concretely(pointer, 4)
            .then(|| memory.symbolic_int32_load(pointer))
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
                let positive_minus_one = right == Bitvector32Term::Constant(1)
                    && (self.has_condition_fact(
                        ConditionTerm::signed_greater_than(left.clone(), zero.clone()),
                        true,
                    ) || self.has_lower_bound_above(&left, &zero));
                (ordered_nonnegative || positive_minus_one).then_some(false)
            }
            ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                if right.as_ref() == &Bitvector32Term::Constant(1) {
                    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
                    let left = left.as_ref().clone();
                    // Keep the direct increment certificate ahead of general
                    // interval reconstruction. Loop execution commonly has
                    // an exact strict bound on a materialized local even when
                    // that bound is awkward to transport into a full range.
                    let has_strict_upper_bound =
                        self.condition_facts.iter().any(|(condition, value)| {
                            match (condition, value) {
                                (ConditionTerm::Bitvector32SignedLessThan(fact_left, _), true) => {
                                    fact_left.as_ref() == &left
                                }
                                (
                                    ConditionTerm::Bitvector32SignedGreaterThan(_, fact_left),
                                    true,
                                ) => fact_left.as_ref() == &left,
                                _ => false,
                            }
                        });
                    let has_direct_nonoverflowing_upper_bound =
                        self.condition_facts.iter().any(|(condition, value)| {
                            matches!(
                                (condition, value),
                                (ConditionTerm::Bitvector32SignedLessEqual(fact_left, upper), true)
                                    if fact_left.as_ref() == &left
                                        && signed_bitvector_constant(upper)
                                            .is_some_and(|upper| upper < i64::from(i32::MAX))
                            )
                        });
                    return (has_strict_upper_bound
                        || has_direct_nonoverflowing_upper_bound
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
