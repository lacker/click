use super::*;

impl PureFactContext {
    /// Decides a condition against this fact set, memoizing results by the
    /// fact set's content identity.
    ///
    /// A `Some` answer is evidence found in the facts and stays valid no
    /// matter how the search was pruned. A `None` computed under an ambient
    /// truncation (fuel, depth guards, cycle cuts — see
    /// [`note_search_truncation`]) is path-dependent and is not cached.
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
                if let ConditionTerm::Bitvector32Equal(left, right) = condition
                    && super::super::super::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                        left,
                        right,
                        self,
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
                        .or_else(|| self.decide_from_order_facts(condition));
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
        let matched = self
            .condition_facts
            .iter()
            .find(|(fact, fact_value)| {
                **fact_value == value
                    && (*fact == &condition || self.condition_matches(fact, &condition))
            })
            .map(|(fact, fact_value)| Proposition::ConditionIs(fact.clone(), *fact_value));
        if let Some(proposition) = matched {
            record_implicit_reasoning_provenance(self, &proposition);
            true
        } else {
            false
        }
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
        let mut pending = vec![term.clone()];
        let mut visited = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            if let Some(value) = current.as_const() {
                return Some(value);
            }
            for (condition, value) in self.condition_facts.iter() {
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
        let memo_id = ambient_assumptions_memo_id(self);
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
        let equality_index = self.bitvector_equality_index();
        // Walked from both ends: a load variable's congruence edge points
        // only toward the lowered address, so the meeting vertex may be
        // reachable from one side alone.
        let mut left_class = BTreeSet::new();
        let mut stack = vec![equality_graph_term_key(left)];
        while let Some(term) = stack.pop() {
            if !left_class.insert(term.clone()) {
                continue;
            }
            if let Some(neighbors) = equality_index.get(&term) {
                stack.extend(neighbors.keys().cloned());
            }
            if let Some(congruent) = self.load_variable_congruence_neighbor(&term) {
                stack.push(congruent);
            }
        }
        let mut seen = BTreeSet::new();
        let mut stack = vec![equality_graph_term_key(right)];
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            if left_class.contains(&term) {
                return true;
            }
            if let Some(neighbors) = equality_index.get(&term) {
                stack.extend(neighbors.keys().cloned());
            }
            if let Some(congruent) = self.load_variable_congruence_neighbor(&term) {
                stack.push(congruent);
            }
        }

        false
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
        for (condition, value) in self.condition_facts.iter() {
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
        match self.signed_constant_after_equality_normalization_inner(
            term,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        ) {
            SignedConstantResolution::Known(value) => Some(value),
            SignedConstantResolution::Unknown | SignedConstantResolution::Ambiguous => None,
        }
    }

    /// One walk resolves each term once: `resolved` holds the terms the
    /// walk has finished, `resolving` the terms in progress. A term reached
    /// again while in progress is a cycle through the equality facts and
    /// resolves to nothing on that path. The walk's work is therefore the
    /// number of distinct terms the facts connect to the query, each scanned
    /// once, with no node budget.
    fn signed_constant_after_equality_normalization_inner(
        &self,
        term: &Bitvector32Term,
        resolving: &mut BTreeSet<Bitvector32Term>,
        resolved: &mut BTreeMap<Bitvector32Term, SignedConstantResolution>,
    ) -> SignedConstantResolution {
        if let Some(done) = resolved.get(term) {
            return done.clone();
        }
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
                resolved,
                Bitvector32Term::add,
            ),
            Bitvector32Term::Subtract(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                resolved,
                Bitvector32Term::subtract,
            ),
            Bitvector32Term::Multiply(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                resolved,
                Bitvector32Term::multiply,
            ),
            Bitvector32Term::Divide(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                resolved,
                Bitvector32Term::divide,
            ),
            Bitvector32Term::Remainder(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                resolved,
                Bitvector32Term::remainder,
            ),
            Bitvector32Term::ShiftLeft(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                resolved,
                Bitvector32Term::shift_left,
            ),
            Bitvector32Term::ArithmeticShiftRight(left, right) => self
                .signed_binary_constant_known_equal(
                    left,
                    right,
                    resolving,
                    resolved,
                    Bitvector32Term::arithmetic_shift_right,
                ),
            Bitvector32Term::BitwiseAnd(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                resolved,
                Bitvector32Term::bitwise_and,
            ),
            Bitvector32Term::BitwiseOr(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                resolved,
                Bitvector32Term::bitwise_or,
            ),
            Bitvector32Term::BitwiseXor(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                resolved,
                Bitvector32Term::bitwise_xor,
            ),
            Bitvector32Term::BitwiseNot(value) => self
                .signed_constant_after_equality_normalization_inner(value, resolving, resolved)
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
                    resolved,
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
        // A load variable is gated exactly as the load it represents: without
        // the gate every equality fact in the context is a deep-equality
        // candidate for every load variable, which is quadratic in the facts.
        let term_view = crate::kernel::eval::viewed_as_memory_load(term);
        let plausibly_equal = |candidate: &Bitvector32Term| {
            if candidate == term {
                return true;
            }
            let candidate_view = crate::kernel::eval::viewed_as_memory_load(candidate);
            match (
                term_view.as_ref().unwrap_or(term),
                candidate_view.as_ref().unwrap_or(candidate),
            ) {
                (
                    Bitvector32Term::MemoryLoad(_, term_pointer),
                    Bitvector32Term::MemoryLoad(_, candidate_pointer),
                ) => pointers_equal_ignoring_memories(term_pointer, candidate_pointer),
                (Bitvector32Term::MemoryLoad(_, _), _) | (_, Bitvector32Term::MemoryLoad(_, _)) => {
                    false
                }
                _ => true,
            }
        };
        for (condition, value) in self.condition_facts.iter() {
            let (ConditionTerm::Bitvector32Equal(left, right), true) = (condition, value) else {
                continue;
            };
            if plausibly_equal(left) && self.bitvector_terms_proven_equal(term, left) {
                result = result.merge(self.signed_constant_after_equality_normalization_inner(
                    right, resolving, resolved,
                ));
            }
            if plausibly_equal(right) && self.bitvector_terms_proven_equal(term, right) {
                result =
                    result.merge(self.signed_constant_after_equality_normalization_inner(
                        left, resolving, resolved,
                    ));
            }
        }

        resolving.remove(term);
        resolved.insert(term.clone(), result.clone());
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
        resolved: &mut BTreeMap<Bitvector32Term, SignedConstantResolution>,
        operation: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
    ) -> SignedConstantResolution {
        let left =
            self.signed_constant_after_equality_normalization_inner(left, resolving, resolved);
        let right =
            self.signed_constant_after_equality_normalization_inner(right, resolving, resolved);
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
}
