use super::prelude::*;
use std::cell::Cell;

// Global equality resolution can re-enter itself through snapshot and alias
// facts. Two levels retain the framed symbolic-load cases while making failed
// searches terminate conservatively instead of overflowing the stack.
const MEMORY_LOAD_EQUALITY_DEPTH_LIMIT: usize = 2;

thread_local! {
    static MEMORY_LOAD_EQUALITY_DEPTH: Cell<usize> = const { Cell::new(0) };
}

struct MemoryLoadEqualityDepthGuard;

impl MemoryLoadEqualityDepthGuard {
    fn enter() -> Option<Self> {
        MEMORY_LOAD_EQUALITY_DEPTH.with(|depth| {
            let current = depth.get();
            if current >= MEMORY_LOAD_EQUALITY_DEPTH_LIMIT {
                return None;
            }
            depth.set(current + 1);
            Some(Self)
        })
    }
}

impl Drop for MemoryLoadEqualityDepthGuard {
    fn drop(&mut self) {
        MEMORY_LOAD_EQUALITY_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

fn bitvector_terms_equal_after_exact_materialization(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    fn normalize(term: &Bitvector32Term) -> Bitvector32Term {
        let mut current = term.clone();
        for _ in 0..64 {
            let Bitvector32Term::MemoryLoad(memory, pointer) = &current else {
                break;
            };
            let Some(CValue::Int32(value)) = memory.known_value(pointer) else {
                break;
            };
            if value == current {
                break;
            }
            current = value;
        }
        current
    }

    normalize(left) == normalize(right)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SignedConstantResolution {
    Unknown,
    Known(i64),
    Ambiguous,
}

impl SignedConstantResolution {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Ambiguous, _) | (_, Self::Ambiguous) => Self::Ambiguous,
            (Self::Unknown, resolution) | (resolution, Self::Unknown) => resolution,
            (Self::Known(left), Self::Known(right)) if left == right => Self::Known(left),
            (Self::Known(_), Self::Known(_)) => Self::Ambiguous,
        }
    }

    fn from_term(term: Bitvector32Term) -> Self {
        signed_bitvector_constant(&term).map_or(Self::Unknown, Self::Known)
    }

    fn map(self, operation: impl FnOnce(i64) -> Bitvector32Term) -> Self {
        match self {
            Self::Known(value) => Self::from_term(operation(value)),
            Self::Unknown => Self::Unknown,
            Self::Ambiguous => Self::Ambiguous,
        }
    }
}

#[cfg(test)]
impl Proposition {
    pub(super) fn peel_implications(&self) -> &Self {
        match self {
            Self::Implies(_, body) => body.peel_implications(),
            _ => self,
        }
    }
}

impl Assumptions {
    pub fn new() -> Self {
        Self::default()
    }

    /// Keep contextual loadability consequences as explicit proof obligations
    /// instead of silently discharging them while symbolic execution is being
    /// planned.
    ///
    /// Condition reasoning is unchanged: this flag only controls the
    /// obligation boundary used by the evaluator.
    pub(crate) fn defer_non_exact_loadability_obligations(mut self) -> Self {
        self.defer_non_exact_loadability_obligations = true;
        self
    }

    pub(super) fn should_defer_non_exact_loadability_obligations(&self) -> bool {
        self.defer_non_exact_loadability_obligations
    }

    /// Surface-certificate synthesis uses this only to structurally lower a
    /// candidate spelling before comparing it with an already-certified
    /// kernel proposition. Ordinary proof checking must not enable it.
    pub(crate) fn allow_symbolic_contract_loads(mut self) -> Self {
        self.allow_symbolic_contract_loads = true;
        self
    }

    pub(crate) fn should_allow_symbolic_contract_loads(&self) -> bool {
        self.allow_symbolic_contract_loads
    }

    pub(crate) fn defer_non_exact_condition_reasoning(mut self) -> Self {
        self.defer_non_exact_condition_reasoning = true;
        self
    }

    pub(super) fn should_defer_non_exact_condition_reasoning(&self) -> bool {
        self.defer_non_exact_condition_reasoning
    }

    pub(crate) fn prefer_symbolic_external_loads(mut self) -> Self {
        self.prefer_symbolic_external_loads = true;
        self
    }

    pub(super) fn should_prefer_symbolic_external_loads(&self) -> bool {
        self.prefer_symbolic_external_loads
    }

    pub(super) fn proves_exact(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.condition_facts.get(condition) == Some(value)
            }
            Proposition::And(left, right) => self.proves_exact(left) && self.proves_exact(right),
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.condition_facts.get(condition) == Some(&!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            _ => self.prop_facts.contains(proposition),
        }
    }

    pub fn assume_condition(mut self, condition: ConditionTerm, value: bool) -> Self {
        if let ConditionTerm::Bitvector32Equal(left, right) = &condition
            && let Some((left, right)) = bitvector_equality_after_additive_cancellation(left, right)
        {
            self = self.assume_condition(ConditionTerm::equal(left, right), value);
        }
        self.condition_facts.insert(condition, value);
        self
    }

    pub fn assume_proposition(mut self, proposition: Proposition) -> Self {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self = self.assume_condition(condition, value);
            }
            Proposition::And(left, right) => {
                self = self.assume_proposition(*left);
                self = self.assume_proposition(*right);
            }
            Proposition::Not(body) => match *body {
                Proposition::ConditionIs(condition, value) => {
                    self = self.assume_condition(condition, !value);
                }
                body => {
                    self.prop_facts.insert(Proposition::Not(Box::new(body)));
                }
            },
            proposition => {
                self.prop_facts.insert(proposition);
            }
        }
        self
    }

    pub fn pure_facts(&self) -> Vec<Proposition> {
        let mut facts = self
            .condition_facts
            .iter()
            .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), *value))
            .collect::<Vec<_>>();
        facts.extend(self.prop_facts.iter().cloned());
        facts
    }

    pub(super) fn includes(&self, required: &Self) -> bool {
        required
            .condition_facts
            .iter()
            .all(|(condition, value)| self.condition_facts.get(condition) == Some(value))
            && required
                .prop_facts
                .iter()
                .all(|proposition| self.prop_facts.contains(proposition))
    }

    pub(super) fn decide(&self, condition: &ConditionTerm) -> Option<bool> {
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

    pub(super) fn decide_intrinsically(condition: &ConditionTerm) -> Option<bool> {
        Self::new().decide(condition)
    }

    pub(super) fn has_condition_fact(&self, condition: ConditionTerm, value: bool) -> bool {
        self.condition_facts.get(&condition) == Some(&value)
            || self.condition_facts.iter().any(|(fact, fact_value)| {
                *fact_value == value && self.condition_matches(fact, &condition)
            })
    }

    pub(super) fn exact_condition_value(&self, condition: &ConditionTerm) -> Option<bool> {
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

    pub(super) fn decide_bitvector_equality_shallow(
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

    pub(super) fn bitvector_terms_equal_from_facts(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }

        let mut seen = BTreeSet::new();
        let mut stack = vec![left.clone()];
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            if &term == right {
                return true;
            }
            for (condition, value) in &self.condition_facts {
                if !*value {
                    continue;
                }
                let (fact_left, fact_right) = match condition {
                    ConditionTerm::Bitvector32Equal(fact_left, fact_right) => {
                        (fact_left.as_ref().clone(), fact_right.as_ref().clone())
                    }
                    ConditionTerm::PointerOffsetEqual(fact_left, fact_right) => {
                        let (Some(fact_left), Some(fact_right)) = (
                            int32_element_index_from_offset(fact_left),
                            int32_element_index_from_offset(fact_right),
                        ) else {
                            continue;
                        };
                        (fact_left, fact_right)
                    }
                    _ => continue,
                };
                if fact_left == term {
                    stack.push(fact_right.clone());
                }
                if fact_right == term {
                    stack.push(fact_left);
                }
            }
        }

        false
    }

    pub(super) fn simplify_condition_under_assumptions(
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

    pub(super) fn simplify_bitvector_under_assumptions(
        &self,
        term: &Bitvector32Term,
    ) -> Bitvector32Term {
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
            Bitvector32Term::MemoryLoad(memory, pointer) => {
                Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone())
            }
        }
    }

    pub(super) fn order_facts_force_equal(
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

    pub(super) fn range_facts_force_equal(
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

    pub(super) fn signed_constant_known_equal(&self, term: &Bitvector32Term) -> Option<i64> {
        if let Some(value) = signed_bitvector_constant(term) {
            return Some(value);
        }

        for (condition, value) in &self.condition_facts {
            let (ConditionTerm::Bitvector32Equal(left, right), true) = (condition, value) else {
                continue;
            };
            if self.bitvector_terms_proven_equal(term, left)
                && let Some(value) = signed_bitvector_constant(right)
            {
                return Some(value);
            }
            if self.bitvector_terms_proven_equal(term, right)
                && let Some(value) = signed_bitvector_constant(left)
            {
                return Some(value);
            }
        }

        None
    }

    fn signed_constant_after_equality_normalization(&self, term: &Bitvector32Term) -> Option<i64> {
        match self.signed_constant_after_equality_normalization_inner(term, &mut BTreeSet::new()) {
            SignedConstantResolution::Known(value) => Some(value),
            SignedConstantResolution::Unknown | SignedConstantResolution::Ambiguous => None,
        }
    }

    fn signed_constant_after_equality_normalization_inner(
        &self,
        term: &Bitvector32Term,
        resolving: &mut BTreeSet<Bitvector32Term>,
    ) -> SignedConstantResolution {
        if let Some(value) = signed_bitvector_constant(term) {
            return SignedConstantResolution::Known(value);
        }
        if !resolving.insert(term.clone()) {
            return SignedConstantResolution::Unknown;
        }

        let mut result = match term {
            Bitvector32Term::Add(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::add,
            ),
            Bitvector32Term::Subtract(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::subtract,
            ),
            Bitvector32Term::Multiply(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::multiply,
            ),
            Bitvector32Term::Divide(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::divide,
            ),
            Bitvector32Term::Remainder(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::remainder,
            ),
            Bitvector32Term::ShiftLeft(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::shift_left,
            ),
            Bitvector32Term::ArithmeticShiftRight(left, right) => self
                .signed_binary_constant_known_equal(
                    left,
                    right,
                    resolving,
                    Bitvector32Term::arithmetic_shift_right,
                ),
            Bitvector32Term::BitwiseAnd(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::bitwise_and,
            ),
            Bitvector32Term::BitwiseOr(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::bitwise_or,
            ),
            Bitvector32Term::BitwiseXor(left, right) => self.signed_binary_constant_known_equal(
                left,
                right,
                resolving,
                Bitvector32Term::bitwise_xor,
            ),
            Bitvector32Term::BitwiseNot(value) => self
                .signed_constant_after_equality_normalization_inner(value, resolving)
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
                ),
                None => SignedConstantResolution::Unknown,
            },
            _ => SignedConstantResolution::Unknown,
        };

        for (condition, value) in &self.condition_facts {
            let (ConditionTerm::Bitvector32Equal(left, right), true) = (condition, value) else {
                continue;
            };
            if self.bitvector_terms_proven_equal(term, left) {
                result = result.merge(
                    self.signed_constant_after_equality_normalization_inner(right, resolving),
                );
            }
            if self.bitvector_terms_proven_equal(term, right) {
                result = result.merge(
                    self.signed_constant_after_equality_normalization_inner(left, resolving),
                );
            }
        }

        resolving.remove(term);
        result
    }

    fn signed_binary_constant_known_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        resolving: &mut BTreeSet<Bitvector32Term>,
        operation: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
    ) -> SignedConstantResolution {
        let left = self.signed_constant_after_equality_normalization_inner(left, resolving);
        let right = self.signed_constant_after_equality_normalization_inner(right, resolving);
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

    pub(super) fn decide_signed_comparison_from_equal_constants(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        compare: impl FnOnce(i64, i64) -> bool,
    ) -> Option<bool> {
        let left = self.signed_constant_known_equal(left)?;
        let right = self.signed_constant_known_equal(right)?;
        Some(compare(left, right))
    }

    pub(super) fn decide_from_order_facts(&self, condition: &ConditionTerm) -> Option<bool> {
        match condition {
            ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerEqual(left, right) => {
                left.blocks_proven_distinct(right).then_some(false)
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
                    || left.add_const_base(1).is_some_and(|base| {
                        right == Bitvector32Term::Constant(0)
                            && self.has_condition_fact(
                                ConditionTerm::signed_greater_equal(
                                    base,
                                    Bitvector32Term::Constant(0),
                                ),
                                true,
                            )
                    })
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
                    || left.add_const_base(1).is_some_and(|base| {
                        right == Bitvector32Term::Constant(0)
                            && self.has_condition_fact(
                                ConditionTerm::signed_greater_equal(
                                    base,
                                    Bitvector32Term::Constant(0),
                                ),
                                true,
                            )
                    })
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

    pub(super) fn has_order_path(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let order_facts = self.condition_order_facts();
        self.has_order_path_in_facts(left, right, require_strict, &order_facts)
    }

    fn has_exact_order_path(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let order_facts = self.condition_order_facts();
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            if &current == right && (!require_strict || strict_so_far) {
                return true;
            }
            for (edge_left, edge_right, edge_strict) in &order_facts {
                let constant_connection = signed_bitvector_constant(&current)
                    .zip(signed_bitvector_constant(edge_left))
                    .and_then(|(current, edge_left)| {
                        (current <= edge_left).then_some(current < edge_left)
                    });
                if &current == edge_left || constant_connection.is_some() {
                    stack.push((
                        edge_right.clone(),
                        strict_so_far || *edge_strict || constant_connection == Some(true),
                    ));
                }
            }
        }
        false
    }

    pub(super) fn has_order_path_in_facts(
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
            if self.bitvector_terms_equal_for_transport(&current, right)
                && (!require_strict || strict_so_far)
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

    pub(crate) fn decide_condition_for_simp(&self, condition: &ConditionTerm) -> Option<bool> {
        if let Some(value) = self.decide(condition) {
            return Some(value);
        }

        // This stronger normalization is tactic-local. Using it in `decide`
        // would change symbolic execution paths and loop certificates.
        let (left, right, strict) = condition_as_order_fact(condition, true)?;
        self.has_order_path_for_simp(&left, &right, strict)
            .then_some(true)
    }

    fn has_order_path_for_simp(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let order_facts = self.condition_order_facts();
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

    fn order_path_connection_for_simp(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        if self.bitvector_terms_equal_for_simp(left, right) {
            return Some(false);
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

    pub(super) fn condition_order_facts(&self) -> Vec<(Bitvector32Term, Bitvector32Term, bool)> {
        self.condition_facts
            .iter()
            .filter_map(|(condition, value)| condition_as_order_fact(condition, *value))
            .collect()
    }

    pub(super) fn collect_derived_order_facts(
        &self,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        for proposition in &self.prop_facts {
            self.collect_derived_order_facts_from_proposition(proposition, order_facts);
        }
    }

    pub(super) fn collect_derived_order_facts_from_proposition(
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

    pub(super) fn collect_finite_forall_order_facts(
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

    pub(super) fn collect_finite_forall_order_fact_instantiations(
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

    pub(super) fn has_upper_bound_below(
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

    pub(super) fn has_upper_bound_at_or_below(
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

    pub(super) fn has_successor_upper_bound_below(
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

    pub(super) fn has_add_const_upper_bound_below(
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

    pub(super) fn has_add_const_upper_bound_at_or_below(
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

    pub(super) fn subtract_same_const_order_fact(
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

    pub(super) fn has_lower_bound_above(
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
                    self.decide(&ConditionTerm::signed_greater_than(
                        lower.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if self.bitvector_terms_equal_for_transport(fact_left, left) =>
                {
                    self.decide(&ConditionTerm::signed_greater_than(
                        lower.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                _ => false,
            })
    }

    pub(super) fn has_lower_bound_at_or_above(
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

    pub(super) fn has_add_const_lower_bound_above(
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

    pub(super) fn has_add_const_lower_bound_at_or_above(
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

    pub(super) fn positive_offset_is_proven_above(
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

    pub(super) fn positive_subtraction_is_proven_below(
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

    pub(super) fn nonnegative_offset_is_proven_at_or_above(
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

    pub(super) fn memory_loads_proven_equal(
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
        if memories_match_for_pointer_load_under_assumptions(
            left_memory,
            right_memory,
            left_pointer,
            self,
        ) {
            return true;
        }

        if self.memory_snapshots_directly_proven_equal_for_load(
            left_memory,
            right_memory,
            left_pointer,
        ) || self.memory_snapshots_proven_equal_for_load(left_memory, right_memory, left_pointer)
        {
            return true;
        }

        false
    }

    fn memory_snapshots_directly_proven_equal_for_load(
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
                    && pointers
                        .iter()
                        .all(|write| pointers_proven_distinct(write, pointer, self))
            }
            Proposition::CMemoryEffectSummary {
                before,
                after,
                mutable_ranges,
            } => {
                let matches = memory_matches_effect_summary_endpoint(before, left, pointer)
                    && memory_matches_effect_summary_endpoint(after, right, pointer)
                    || memory_matches_effect_summary_endpoint(before, right, pointer)
                        && memory_matches_effect_summary_endpoint(after, left, pointer);
                matches && self.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
            }
            _ => false,
        })
    }

    fn memory_snapshots_proven_equal_for_load(
        &self,
        left: &CMemory,
        right: &CMemory,
        pointer: &Pointer,
    ) -> bool {
        let mut pending = vec![left.clone()];
        let mut visited = BTreeSet::new();

        while let Some(current) = pending.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            if memories_match_for_pointer_load(&current, right, pointer)
                || memories_match_for_pointer_load_under_assumptions(&current, right, pointer, self)
            {
                return true;
            }

            for proposition in &self.prop_facts {
                match proposition {
                    Proposition::CMemoryMutatesOnly {
                        before,
                        after,
                        pointers,
                    } if pointers
                        .iter()
                        .all(|write| pointers_proven_distinct(write, pointer, self)) =>
                    {
                        if memories_match_for_pointer_load(before, &current, pointer) {
                            pending.push(after.clone());
                        }
                        if memories_match_for_pointer_load(after, &current, pointer) {
                            pending.push(before.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        false
    }

    pub(super) fn resolve_memory_load_term(
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

    pub(super) fn resolve_memory_load_value(
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

    pub(super) fn decide_from_overflow_facts(&self, condition: &ConditionTerm) -> Option<bool> {
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
            ConditionTerm::Bitvector32SignedAddOverflows(left, right)
                if right.as_ref() == &Bitvector32Term::Constant(1) =>
            {
                let int_max = Bitvector32Term::Constant(i32::MAX as u32);
                let left = left.as_ref().clone();
                // Any exact strict upper bound on an int32 proves that `left`
                // is not INT_MAX. Check this common increment certificate
                // syntactically before invoking transported order reasoning;
                // the latter may compare large symbolic memory terms.
                let has_strict_upper_bound =
                    self.condition_facts.iter().any(|(condition, value)| {
                        match (condition, value) {
                            (ConditionTerm::Bitvector32SignedLessThan(fact_left, _), true) => {
                                fact_left.as_ref() == &left
                            }
                            (ConditionTerm::Bitvector32SignedGreaterThan(_, fact_left), true) => {
                                fact_left.as_ref() == &left
                            }
                            _ => false,
                        }
                    });
                (has_strict_upper_bound
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(left.clone(), int_max.clone()),
                        true,
                    )
                    || self.has_upper_bound_below(&left, &int_max))
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

    pub fn proves(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }

        if self.prop_facts.contains(proposition) {
            return true;
        }

        let direct = match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide(condition) == Some(*value)
                    || self.proves_condition_from_facts(condition, *value)
            }
            Proposition::And(left, right) => self.proves(left) && self.proves(right),
            Proposition::Or(left, right) => self.proves(left) || self.proves(right),
            Proposition::Not(body) => self.proves_not(body),
            Proposition::Implies(left, right) => self
                .clone()
                .assume_proposition(left.as_ref().clone())
                .proves(right),
            Proposition::ForAll {
                sort: Sort::CInt32,
                body,
                ..
            } => self.proves_finite_forall(proposition) || self.proves(body),
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
            } => self.proves_memory_loadable(memory, base, bytes),
            Proposition::CMemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => self.proves_memory_access(memory, pointer, *byte_width),
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                self.prop_facts.contains(proposition)
                    || self.proves_memory_disjoint(
                        left_base,
                        left_start,
                        left_end,
                        right_base,
                        right_start,
                        right_end,
                    )
                    || self.proves_memory_disjoint_from_resource_separate(
                        left_base,
                        left_start,
                        left_end,
                        right_base,
                        right_start,
                        right_end,
                    )
            }
            Proposition::CResourceSeparate { left, right } => {
                self.prop_facts.contains(proposition) || self.proves_resource_separate(left, right)
            }
            Proposition::CResourceContains { parent, child } => {
                self.prop_facts.contains(proposition)
                    || self.proves_resource_contains(parent, child)
            }
            _ => self.prop_facts.contains(proposition),
        };
        direct
            || self.is_inconsistent()
            || self.proves_by_finite_context_split(proposition)
            || self.proves_by_disjunction_cases(proposition)
    }

    /// Search for an explicit proof tree for a contextual consequence.
    ///
    /// This is the proof-producing counterpart to [`Self::proves`]. Atomic
    /// leaves retain the complete context used to check them; minimizing that
    /// context would require repeated solver calls and is not part of proof
    /// correctness.
    pub fn derive_proposition(&self, proposition: &Proposition) -> Option<PropositionDerivation> {
        self.derive_proposition_using(proposition, false)
    }

    pub fn derive_simp_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        self.derive_proposition_using(proposition, true)
    }

    /// Check one atomic theory consequence against this exact premise set.
    ///
    /// Unlike [`Self::derive_proposition`], this does not introduce logical
    /// structure or attempt finite case splits.
    pub fn derive_atomic_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        self.derive_atomic_proposition_using(proposition, false)
    }

    /// The simplifier's atomic theory check, without structural proof search.
    pub fn derive_simp_atomic_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        self.derive_atomic_proposition_using(proposition, true)
    }

    fn derive_atomic_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivation> {
        self.atomic_derivation_premises(proposition, for_simp)
            .map(|premises| {
                proposition_derivation(
                    proposition,
                    PropositionDerivationRule::ContextualAtomic { premises, for_simp },
                )
            })
    }

    /// Select the range fact that justified a memory-access consequence.
    ///
    /// General solving may inspect several loadability ranges while planning.
    /// A derivation must retain the successful choice so replay does not repeat
    /// that candidate search. Other fact kinds remain available because
    /// pointer/snapshot equality can depend on explicit frame facts.
    fn atomic_derivation_premises(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<Assumptions> {
        let candidate_family = |fact: &Proposition| match proposition {
            Proposition::CMemoryLoadable { .. } | Proposition::CMemoryCanStore { .. } => {
                matches!(fact, Proposition::CMemoryLoadable { .. })
            }
            Proposition::CResourceSeparate { .. } => matches!(
                fact,
                Proposition::CResourceSeparate { .. } | Proposition::CMemoryDisjoint { .. }
            ),
            Proposition::CMemoryDisjoint { .. } => matches!(
                fact,
                Proposition::CMemoryDisjoint { .. } | Proposition::CResourceSeparate { .. }
            ),
            _ => false,
        };
        let candidates = self
            .prop_facts
            .iter()
            .filter(|fact| candidate_family(fact))
            .cloned()
            .collect::<Vec<_>>();
        if candidates.len() > 1 {
            for selected in candidates {
                let mut candidate = self.clone();
                candidate.prop_facts.retain(|fact| !candidate_family(fact));
                candidate.prop_facts.insert(selected);
                if candidate.proves_atomic_for_derivation(proposition, for_simp) {
                    return Some(candidate);
                }
            }
        }
        self.proves_atomic_for_derivation(proposition, for_simp)
            .then(|| self.clone())
    }

    fn derive_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivation> {
        if solve_builtin_prop(proposition) {
            return Some(proposition_derivation(
                proposition,
                PropositionDerivationRule::ContextFree,
            ));
        }
        if self.is_inconsistent() {
            return Some(proposition_derivation(
                proposition,
                PropositionDerivationRule::Explosion {
                    premises: self.clone(),
                },
            ));
        }

        let direct = match proposition {
            Proposition::And(left, right) => self
                .derive_proposition_using(left, for_simp)
                .zip(self.derive_proposition_using(right, for_simp))
                .map(|(left, right)| PropositionDerivationRule::And {
                    left: Box::new(left),
                    right: Box::new(right),
                }),
            Proposition::Or(left, right) => self
                .derive_proposition_using(left, for_simp)
                .map(|proof| PropositionDerivationRule::OrLeft(Box::new(proof)))
                .or_else(|| {
                    self.derive_proposition_using(right, for_simp)
                        .map(|proof| PropositionDerivationRule::OrRight(Box::new(proof)))
                }),
            Proposition::Not(body) => match body.as_ref() {
                Proposition::Not(inner) => self
                    .derive_proposition_using(inner, for_simp)
                    .map(|proof| PropositionDerivationRule::DoubleNegation(Box::new(proof))),
                _ => self
                    .atomic_derivation_premises(proposition, for_simp)
                    .map(|premises| PropositionDerivationRule::ContextualAtomic {
                        premises,
                        for_simp,
                    }),
            },
            Proposition::Implies(left, right) => {
                let antecedent = left.as_ref().clone();
                self.clone()
                    .assume_proposition(antecedent.clone())
                    .derive_proposition_using(right, for_simp)
                    .map(|body| PropositionDerivationRule::Implies {
                        antecedent,
                        body: Box::new(body),
                    })
                    .or_else(|| {
                        self.derive_proposition_using(
                            &Proposition::Not(Box::new(left.as_ref().clone())),
                            for_simp,
                        )
                        .map(|proof| {
                            PropositionDerivationRule::ImpliesFalseAntecedent(Box::new(proof))
                        })
                    })
            }
            Proposition::ForAll { body, .. } => self
                .derive_finite_forall(proposition, for_simp)
                .or_else(|| {
                    self.derive_proposition_using(body, for_simp)
                        .map(|proof| PropositionDerivationRule::ForAllBody(Box::new(proof)))
                }),
            _ => self
                .atomic_derivation_premises(proposition, for_simp)
                .map(|premises| PropositionDerivationRule::ContextualAtomic { premises, for_simp }),
        };
        if let Some(rule) = direct {
            return Some(proposition_derivation(proposition, rule));
        }
        if let Some(rule) = self.derive_by_finite_context_split(proposition, for_simp) {
            return Some(proposition_derivation(proposition, rule));
        }
        self.derive_by_disjunction_cases(proposition, for_simp)
            .map(|rule| proposition_derivation(proposition, rule))
    }

    fn proves_atomic_without_search(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide(condition) == Some(*value)
                    || self.proves_condition_from_facts(condition, *value)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide(condition) == Some(!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
            } => self.proves_memory_loadable(memory, base, bytes),
            Proposition::CMemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => self.proves_memory_access(memory, pointer, *byte_width),
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                self.prop_facts.contains(proposition)
                    || self.proves_memory_disjoint(
                        left_base,
                        left_start,
                        left_end,
                        right_base,
                        right_start,
                        right_end,
                    )
                    || self.proves_memory_disjoint_from_resource_separate(
                        left_base,
                        left_start,
                        left_end,
                        right_base,
                        right_start,
                        right_end,
                    )
            }
            Proposition::CResourceSeparate { left, right } => {
                self.prop_facts.contains(proposition) || self.proves_resource_separate(left, right)
            }
            Proposition::CResourceContains { parent, child } => {
                self.prop_facts.contains(proposition)
                    || self.proves_resource_contains(parent, child)
            }
            Proposition::And(_, _)
            | Proposition::Or(_, _)
            | Proposition::Implies(_, _)
            | Proposition::ForAll { .. } => false,
            _ => self.prop_facts.contains(proposition),
        }
    }

    fn proves_atomic_for_derivation(&self, proposition: &Proposition, for_simp: bool) -> bool {
        if for_simp
            && let Proposition::ConditionIs(condition, value) = proposition
            && self.decide_condition_for_simp(condition) == Some(*value)
        {
            return true;
        }
        self.proves_atomic_without_search(proposition)
    }

    fn derive_finite_forall(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        let instances = self.finite_forall_instantiations(proposition);
        if instances.is_empty() {
            return None;
        }
        instances
            .iter()
            .map(|instance| self.derive_proposition_using(instance, for_simp))
            .collect::<Option<Vec<_>>>()
            .map(|instances| PropositionDerivationRule::FiniteForAll { instances })
    }

    fn derive_by_finite_context_split(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        let mut variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut variables);
        let mut candidates = variables
            .into_iter()
            .filter_map(|variable| {
                self.finite_context_range(variable)
                    .map(|range| (variable, range))
            })
            .filter(|(_, range)| range.lower <= range.upper)
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(_, range)| range.upper - range.lower);

        let (variable, range) = candidates.into_iter().next()?;
        let width = usize::try_from(range.upper - range.lower + 1).ok()?;
        if width > FINITE_CONTEXT_SPLIT_LIMIT {
            return None;
        }
        let propositions = (range.lower..=range.upper)
            .map(|value| {
                substitute_bitvector_variable_in_proposition(
                    proposition,
                    variable,
                    &signed_i64_bitvector_constant(value),
                )
            })
            .collect::<Vec<_>>();
        if propositions.iter().all(|instance| instance == proposition) {
            return None;
        }
        let instances = propositions
            .iter()
            .map(|instance| self.derive_proposition_using(instance, for_simp))
            .collect::<Option<Vec<_>>>()?;
        Some(PropositionDerivationRule::FiniteContextSplit {
            variable,
            lower: range.lower,
            upper: range.upper,
            instances,
        })
    }

    fn derive_by_disjunction_cases(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        if !matches!(proposition, Proposition::Or(_, _)) {
            return None;
        }
        for disjunction in &self.prop_facts {
            let mut cases = Vec::new();
            collect_or_cases(disjunction, &mut cases);
            if cases.len() < 2 || cases.len() > DISJUNCTION_CASE_LIMIT {
                continue;
            }
            let mut base = self.clone();
            base.prop_facts.remove(disjunction);
            let Some(proofs) = cases
                .iter()
                .map(|case| {
                    base.clone()
                        .assume_proposition(case.clone())
                        .derive_proposition_using(proposition, for_simp)
                })
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            return Some(PropositionDerivationRule::DisjunctionCases {
                disjunction: disjunction.clone(),
                cases: proofs,
            });
        }
        None
    }

    pub(super) fn proves_by_disjunction_cases(&self, proposition: &Proposition) -> bool {
        if !matches!(proposition, Proposition::Or(_, _)) {
            return false;
        }

        for disjunction in &self.prop_facts {
            let mut cases = Vec::new();
            collect_or_cases(disjunction, &mut cases);
            if cases.len() < 2 || cases.len() > DISJUNCTION_CASE_LIMIT {
                continue;
            }

            let mut base = self.clone();
            base.prop_facts.remove(disjunction);
            if cases.iter().all(|case| {
                base.clone()
                    .assume_proposition(case.clone())
                    .proves(proposition)
            }) {
                return true;
            }
        }
        false
    }

    pub(super) fn proves_finite_forall(&self, proposition: &Proposition) -> bool {
        let mut variables = Vec::new();
        let body = collect_forall_chain(proposition, &mut variables);
        if variables.is_empty() {
            return false;
        }
        let Some(ranges) = finite_forall_ranges(&variables, body) else {
            return false;
        };
        let Some(instantiation_count) = ranges.iter().try_fold(1usize, |count, range| {
            let width = usize::try_from(range.upper - range.lower + 1).ok()?;
            count.checked_mul(width)
        }) else {
            return false;
        };
        if instantiation_count > FINITE_FORALL_INSTANTIATION_LIMIT {
            return false;
        }

        let mut values = Vec::with_capacity(variables.len());
        self.proves_finite_forall_instantiations(body, &variables, &ranges, &mut values)
    }

    pub(super) fn proves_finite_forall_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
    ) -> bool {
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for (variable, value) in variables.iter().zip(values.iter()) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &signed_i64_bitvector_constant(*value),
                );
            }
            return self.proves(&instantiated);
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            if !self.proves_finite_forall_instantiations(body, variables, ranges, values) {
                values.pop();
                return false;
            }
            values.pop();
        }
        true
    }

    pub(super) fn proves_by_finite_context_split(&self, proposition: &Proposition) -> bool {
        let mut variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut variables);
        let mut candidates = variables
            .into_iter()
            .filter_map(|variable| {
                self.finite_context_range(variable)
                    .map(|range| (variable, range))
            })
            .filter(|(_, range)| range.lower <= range.upper)
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(_, range)| range.upper - range.lower);

        let Some((variable, range)) = candidates.into_iter().next() else {
            return false;
        };
        let Ok(width) = usize::try_from(range.upper - range.lower + 1) else {
            return false;
        };
        if width > FINITE_CONTEXT_SPLIT_LIMIT {
            return false;
        }

        let instances = (range.lower..=range.upper)
            .map(|value| {
                substitute_bitvector_variable_in_proposition(
                    proposition,
                    variable,
                    &signed_i64_bitvector_constant(value),
                )
            })
            .collect::<Vec<_>>();
        if instances
            .iter()
            .all(|instantiated| instantiated == proposition)
        {
            return false;
        }

        instances
            .iter()
            .all(|instantiated| self.proves(instantiated))
    }

    pub(super) fn finite_context_range(&self, variable: Variable) -> Option<FiniteForAllRange> {
        let mut range = IntegerRangeFacts::default();
        for (condition, value) in &self.condition_facts {
            let Some((left, right, strict)) = condition_as_order_fact(condition, *value) else {
                continue;
            };
            match (bitvector_variable(&left), signed_bitvector_constant(&right)) {
                (Some(fact_variable), Some(bound)) if fact_variable == variable => {
                    let upper = if strict { bound.checked_sub(1)? } else { bound };
                    range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
                }
                _ => {}
            }
            match (signed_bitvector_constant(&left), bitvector_variable(&right)) {
                (Some(bound), Some(fact_variable)) if fact_variable == variable => {
                    let lower = if strict { bound.checked_add(1)? } else { bound };
                    range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
                }
                _ => {}
            }
        }

        let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
            return None;
        };
        Some(FiniteForAllRange { lower, upper })
    }

    pub(super) fn proves_condition_from_facts(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact_condition, fact_value)| {
                fact_value == &value && self.condition_matches(fact_condition, condition)
            })
            || self
                .prop_facts
                .iter()
                .any(|proposition| self.proposition_proves_condition(proposition, condition, value))
            || self.proves_condition_from_derived_order_facts(condition, value)
    }

    pub(super) fn proves_condition_from_derived_order_facts(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        let Some((left, right, strict)) = condition_as_order_fact(condition, value) else {
            return false;
        };
        let mut order_facts = self.condition_order_facts();
        self.collect_derived_order_facts(&mut order_facts);
        self.has_order_path_in_facts(&left, &right, strict, &order_facts)
    }

    pub(super) fn proposition_proves_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        match proposition {
            Proposition::ConditionIs(fact_condition, fact_value) => {
                fact_value == &value && self.condition_matches(fact_condition, condition)
            }
            Proposition::And(left, right) => {
                self.proposition_proves_condition(left, condition, value)
                    || self.proposition_proves_condition(right, condition, value)
            }
            Proposition::Implies(left, right) => {
                self.proves_without_prop_facts(left)
                    && self.proposition_proves_condition(right, condition, value)
            }
            Proposition::ForAll { body, .. } => {
                self.proposition_proves_condition(body, condition, value)
                    || self
                        .forall_instantiations_for_condition(proposition, condition)
                        .iter()
                        .any(|body| self.proposition_proves_condition(body, condition, value))
                    || self
                        .finite_forall_instantiations(proposition)
                        .iter()
                        .any(|body| self.proposition_proves_condition(body, condition, value))
            }
            _ => false,
        }
    }

    pub(super) fn finite_forall_instantiations(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        let mut variables = Vec::new();
        let body = collect_forall_chain(proposition, &mut variables);
        if variables.is_empty() {
            return Vec::new();
        }
        let Some(ranges) = finite_forall_ranges(&variables, body) else {
            return Vec::new();
        };
        let Some(instantiation_count) = ranges.iter().try_fold(1usize, |count, range| {
            let width = usize::try_from(range.upper - range.lower + 1).ok()?;
            count.checked_mul(width)
        }) else {
            return Vec::new();
        };
        if instantiation_count > FINITE_FORALL_INSTANTIATION_LIMIT {
            return Vec::new();
        }

        let mut values = Vec::with_capacity(variables.len());
        let mut instantiations = Vec::with_capacity(instantiation_count);
        self.collect_finite_forall_condition_instantiations(
            body,
            &variables,
            &ranges,
            &mut values,
            &mut instantiations,
        );
        instantiations
    }

    pub(super) fn collect_finite_forall_condition_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
        instantiations: &mut Vec<Proposition>,
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
            instantiations.push(instantiated);
            return;
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            self.collect_finite_forall_condition_instantiations(
                body,
                variables,
                ranges,
                values,
                instantiations,
            );
            values.pop();
        }
    }

    pub(super) fn forall_instantiations_for_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
    ) -> Vec<Proposition> {
        let Proposition::ForAll { var, body, .. } = proposition else {
            return Vec::new();
        };
        let mut variables = BTreeSet::new();
        collect_condition_bitvector_variables(condition, &mut variables);
        variables
            .into_iter()
            .filter(|candidate| candidate != var)
            .map(|candidate| {
                substitute_bitvector_variable_in_proposition(
                    body,
                    *var,
                    &Bitvector32Term::Variable(candidate),
                )
            })
            .collect()
    }

    pub(super) fn condition_matches(&self, fact: &ConditionTerm, target: &ConditionTerm) -> bool {
        if fact == target {
            return true;
        }

        match (fact, target) {
            (
                ConditionTerm::Bitvector32Equal(fact_left, fact_right),
                ConditionTerm::Bitvector32Equal(target_left, target_right),
            ) => {
                let fact_left = fact_left.as_ref();
                let fact_right = fact_right.as_ref();
                let target_left = target_left.as_ref();
                let target_right = target_right.as_ref();
                fact_right == target_right
                    && self.bitvector_terms_equal_for_transport(fact_left, target_left)
                    || fact_right == target_left
                        && self.bitvector_terms_equal_for_transport(fact_left, target_right)
                    || fact_left == target_right
                        && self.bitvector_terms_equal_for_transport(fact_right, target_left)
                    || fact_left == target_left
                        && self.bitvector_terms_equal_for_transport(fact_right, target_right)
                    || self.bitvector_terms_equal_for_transport(fact_left, target_left)
                        && self.bitvector_terms_equal_for_transport(fact_right, target_right)
                    || self.bitvector_terms_equal_for_transport(fact_left, target_right)
                        && self.bitvector_terms_equal_for_transport(fact_right, target_left)
            }
            (
                ConditionTerm::PointerOffsetEqual(fact_left, fact_right),
                ConditionTerm::PointerOffsetEqual(target_left, target_right),
            ) => {
                let fact_left = fact_left.as_ref();
                let fact_right = fact_right.as_ref();
                let target_left = target_left.as_ref();
                let target_right = target_right.as_ref();
                fact_right == target_right
                    && self.pointer_offset_terms_equal_for_transport(fact_left, target_left)
                    || fact_right == target_left
                        && self.pointer_offset_terms_equal_for_transport(fact_left, target_right)
                    || fact_left == target_right
                        && self.pointer_offset_terms_equal_for_transport(fact_right, target_left)
                    || fact_left == target_left
                        && self.pointer_offset_terms_equal_for_transport(fact_right, target_right)
                    || self.pointer_offset_terms_snapshot_equivalent(fact_left, target_left)
                        && self.pointer_offset_terms_snapshot_equivalent(fact_right, target_right)
                    || self.pointer_offset_terms_snapshot_equivalent(fact_left, target_right)
                        && self.pointer_offset_terms_snapshot_equivalent(fact_right, target_left)
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
                self.bitvector_terms_equal_for_transport(fact_left, target_left)
                    && self.bitvector_terms_equal_for_transport(fact_right, target_right)
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
                self.bitvector_terms_equal_for_transport(fact_left, target_right)
                    && self.bitvector_terms_equal_for_transport(fact_right, target_left)
            }
            _ => false,
        }
    }

    pub(super) fn bitvector_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right
            || self.bitvector_if_terms_proven_equal(left, right)
            || self.bitvector_add_terms_proven_equal(left, right)
            || self.count_fold_split_terms_proven_equal(left, right)
            || self.range_fold_terms_alpha_equivalent(left, right)
            || self.memory_loads_proven_equal(left, right)
    }

    pub(super) fn bitvector_terms_equal_for_transport(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if self.bitvector_terms_equal_from_facts(left, right)
            || self.bitvector_terms_proven_equal(left, right)
        {
            return true;
        }

        match (left, right) {
            (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
            | (
                Bitvector32Term::Subtract(left_a, left_b),
                Bitvector32Term::Subtract(right_a, right_b),
            )
            | (
                Bitvector32Term::Multiply(left_a, left_b),
                Bitvector32Term::Multiply(right_a, right_b),
            )
            | (
                Bitvector32Term::Divide(left_a, left_b),
                Bitvector32Term::Divide(right_a, right_b),
            )
            | (
                Bitvector32Term::Remainder(left_a, left_b),
                Bitvector32Term::Remainder(right_a, right_b),
            )
            | (
                Bitvector32Term::ShiftLeft(left_a, left_b),
                Bitvector32Term::ShiftLeft(right_a, right_b),
            )
            | (
                Bitvector32Term::ArithmeticShiftRight(left_a, left_b),
                Bitvector32Term::ArithmeticShiftRight(right_a, right_b),
            )
            | (
                Bitvector32Term::BitwiseAnd(left_a, left_b),
                Bitvector32Term::BitwiseAnd(right_a, right_b),
            )
            | (
                Bitvector32Term::BitwiseOr(left_a, left_b),
                Bitvector32Term::BitwiseOr(right_a, right_b),
            )
            | (
                Bitvector32Term::BitwiseXor(left_a, left_b),
                Bitvector32Term::BitwiseXor(right_a, right_b),
            ) => {
                self.bitvector_terms_equal_for_transport(left_a, right_a)
                    && self.bitvector_terms_equal_for_transport(left_b, right_b)
            }
            (Bitvector32Term::BitwiseNot(left), Bitvector32Term::BitwiseNot(right)) => {
                self.bitvector_terms_equal_for_transport(left, right)
            }
            _ => false,
        }
    }

    fn pointer_offset_terms_equal_for_transport(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        if left == right {
            return true;
        }

        match (left, right) {
            (
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) => left_width == right_width && self.bitvector_terms_equal_for_transport(left, right),
            (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
                self.pointer_offset_terms_equal_for_transport(left_a, right_a)
                    && self.pointer_offset_terms_equal_for_transport(left_b, right_b)
                    || self.pointer_offset_terms_equal_for_transport(left_a, right_b)
                        && self.pointer_offset_terms_equal_for_transport(left_b, right_a)
            }
            _ => false,
        }
    }

    fn pointer_offset_terms_snapshot_equivalent(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        if left == right {
            return true;
        }
        match (left, right) {
            (
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) => left_width == right_width && self.bitvector_terms_snapshot_equivalent(left, right),
            (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
                self.pointer_offset_terms_snapshot_equivalent(left_a, right_a)
                    && self.pointer_offset_terms_snapshot_equivalent(left_b, right_b)
                    || self.pointer_offset_terms_snapshot_equivalent(left_a, right_b)
                        && self.pointer_offset_terms_snapshot_equivalent(left_b, right_a)
            }
            _ => false,
        }
    }

    pub(super) fn has_pointer_offset_snapshot_fact(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        // Keep this deliberately structural and one-hop. Callers use it only
        // to move an already-certified address equality between framed memory
        // snapshots, never to synthesize a new alias relationship.
        self.condition_facts.iter().any(|(condition, value)| {
            if !*value {
                return false;
            }
            let ConditionTerm::PointerOffsetEqual(fact_left, fact_right) = condition else {
                return false;
            };
            self.pointer_offset_terms_snapshot_equivalent(fact_left, left)
                && self.pointer_offset_terms_snapshot_equivalent(fact_right, right)
                || self.pointer_offset_terms_snapshot_equivalent(fact_left, right)
                    && self.pointer_offset_terms_snapshot_equivalent(fact_right, left)
        })
    }

    fn bitvector_terms_snapshot_equivalent(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }
        match (left, right) {
            (Bitvector32Term::MemoryLoad(_, _), Bitvector32Term::MemoryLoad(_, _)) => {
                memory_load_terms_equal_for_fact_transport(left, right, self)
            }
            (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
            | (
                Bitvector32Term::Subtract(left_a, left_b),
                Bitvector32Term::Subtract(right_a, right_b),
            )
            | (
                Bitvector32Term::Multiply(left_a, left_b),
                Bitvector32Term::Multiply(right_a, right_b),
            ) => {
                self.bitvector_terms_snapshot_equivalent(left_a, right_a)
                    && self.bitvector_terms_snapshot_equivalent(left_b, right_b)
            }
            _ => false,
        }
    }

    pub(super) fn bitvector_if_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let (
            Bitvector32Term::If {
                condition: left_condition,
                then_term: left_then,
                else_term: left_else,
            },
            Bitvector32Term::If {
                condition: right_condition,
                then_term: right_then,
                else_term: right_else,
            },
        ) = (left, right)
        else {
            return false;
        };

        (left_condition == right_condition
            || self.condition_matches(left_condition, right_condition)
            || self.condition_matches(right_condition, left_condition))
            && self.bitvector_terms_proven_equal(left_then, right_then)
            && self.bitvector_terms_proven_equal(left_else, right_else)
    }

    pub(super) fn bitvector_add_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if !matches!(left, Bitvector32Term::Add(_, _))
            && !matches!(right, Bitvector32Term::Add(_, _))
        {
            return false;
        }

        let mut left_terms = Vec::new();
        let mut left_constant = 0u32;
        collect_bitvector_add_terms(left, &mut left_terms, &mut left_constant);

        let mut right_terms = Vec::new();
        let mut right_constant = 0u32;
        collect_bitvector_add_terms(right, &mut right_terms, &mut right_constant);

        if left_constant != right_constant || left_terms.len() != right_terms.len() {
            return false;
        }

        for left_term in left_terms {
            let Some(index) = right_terms.iter().position(|right_term| {
                self.bitvector_addend_terms_proven_equal(&left_term, right_term)
            }) else {
                return false;
            };
            right_terms.remove(index);
        }

        right_terms.is_empty()
    }

    pub(super) fn bitvector_addend_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right
            || self.bitvector_if_terms_proven_equal(left, right)
            || self.range_fold_terms_alpha_equivalent(left, right)
            || self.bitvector_terms_equal_from_facts(left, right)
            || self.memory_loads_proven_equal(left, right)
    }

    pub(super) fn count_fold_split_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        count_fold_split_matches(left, right, self) || count_fold_split_matches(right, left, self)
    }

    pub(super) fn range_fold_terms_alpha_equivalent(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        range_fold_terms_alpha_equivalent(left, right, self)
    }

    pub(super) fn proves_without_prop_facts(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) || self.is_inconsistent() {
            return true;
        }

        match proposition {
            Proposition::ConditionIs(condition, value) => self.decide(condition) == Some(*value),
            Proposition::And(left, right) => {
                self.proves_without_prop_facts(left) && self.proves_without_prop_facts(right)
            }
            Proposition::Or(left, right) => {
                self.proves_without_prop_facts(left) || self.proves_without_prop_facts(right)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide(condition) == Some(!*value)
                }
                _ => false,
            },
            _ => false,
        }
    }

    pub(super) fn is_inconsistent(&self) -> bool {
        let mut order_facts = Vec::new();
        let mut equal_facts = Vec::new();
        let mut disequal_facts = Vec::new();
        for (condition, value) in &self.condition_facts {
            match (condition, value) {
                (ConditionTerm::Constant(actual), expected) if actual != expected => return true,
                (ConditionTerm::Bitvector32Equal(left, right), true) => {
                    equal_facts.push((left.as_ref().clone(), right.as_ref().clone()));
                }
                (ConditionTerm::Bitvector32Equal(left, right), false) => {
                    disequal_facts.push((left.as_ref().clone(), right.as_ref().clone()));
                }
                _ => {
                    if let Some(order_fact) = condition_as_order_fact(condition, *value) {
                        order_facts.push(order_fact);
                    }
                }
            }
        }

        let condition_facts = self.condition_facts.iter().collect::<Vec<_>>();
        for left_index in 0..condition_facts.len() {
            for right_index in left_index + 1..condition_facts.len() {
                let ((left_condition, left_value), (right_condition, right_value)) =
                    (condition_facts[left_index], condition_facts[right_index]);
                if left_value != right_value
                    && self.condition_matches(left_condition, right_condition)
                {
                    return true;
                }
            }
        }

        for (equal_left, equal_right) in &equal_facts {
            if disequal_facts
                .iter()
                .any(|(disequal_left, disequal_right)| {
                    (equal_left == disequal_left && equal_right == disequal_right)
                        || (equal_left == disequal_right && equal_right == disequal_left)
                })
            {
                return true;
            }
        }

        for (left, right, strict) in &order_facts {
            if *strict && self.bitvector_terms_proven_equal(left, right) {
                return true;
            }
            if equal_facts.iter().any(|(equal_left, equal_right)| {
                (self.bitvector_terms_proven_equal(left, equal_left)
                    && self.bitvector_terms_proven_equal(right, equal_right))
                    || (self.bitvector_terms_proven_equal(left, equal_right)
                        && self.bitvector_terms_proven_equal(right, equal_left))
            }) && *strict
            {
                return true;
            }
            if order_facts
                .iter()
                .any(|(other_left, other_right, other_strict)| {
                    self.bitvector_terms_proven_equal(left, other_right)
                        && self.bitvector_terms_proven_equal(right, other_left)
                        && (*strict || *other_strict)
                })
            {
                return true;
            }
        }

        if finite_integer_range_exhausted(&order_facts, &equal_facts, &disequal_facts) {
            return true;
        }

        false
    }

    pub(super) fn proves_not(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => self.decide(condition) == Some(!*value),
            Proposition::Not(body) => self.proves(body),
            _ => self
                .prop_facts
                .contains(&Proposition::Not(Box::new(proposition.clone()))),
        }
    }

    pub(super) fn proves_memory_access(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        self.proves_memory_loadable(memory, pointer, &Bitvector32Term::Constant(byte_width))
    }

    pub(super) fn proves_memory_loadable(
        &self,
        memory: &CMemory,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        if bytes
            .as_const()
            .is_some_and(|bytes| memory.access_in_bounds(base, bytes))
        {
            return true;
        }
        if let Some(byte_width) = bytes.as_const()
            && self.proves_access_from_memory_block(memory, base, byte_width)
        {
            return true;
        }

        if self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryLoadable {
                memory: range_memory,
                base: range_base,
                bytes: range_bytes,
            } = proposition
            else {
                return false;
            };

            memory_range_still_available(range_memory, memory, range_base)
                && self.proves_loadable_region_from_structural_range(
                    range_base,
                    range_bytes,
                    base,
                    bytes,
                )
        }) {
            return true;
        }

        self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryLoadable {
                memory: range_memory,
                base: range_base,
                bytes: range_bytes,
            } = proposition
            else {
                return false;
            };

            memory_range_still_available(range_memory, memory, range_base)
                && self.proves_loadable_region_from_range(range_base, range_bytes, base, bytes)
        })
    }

    fn proves_loadable_region_from_structural_range(
        &self,
        range_base: &Pointer,
        range_bytes: &Bitvector32Term,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        if range_base == base && range_bytes == bytes {
            return true;
        }
        if let Some(byte_width) = bytes.as_const()
            && byte_width == 4
            && let Some(index) = base.element_index_from_base(range_base)
            && let Some(element_count) = int32_element_count_from_bytes(range_bytes)
            && let (Some(index), Some(element_count)) = (
                signed_bitvector_constant(&index),
                signed_bitvector_constant(&element_count),
            )
        {
            return 0 <= index && index < element_count;
        }
        let Some(byte_offset) = pointer_byte_offset_from_base(base, range_base) else {
            return false;
        };
        let (Some(byte_offset), Some(bytes), Some(range_bytes)) = (
            signed_bitvector_constant(&byte_offset),
            signed_bitvector_constant(bytes),
            signed_bitvector_constant(range_bytes),
        ) else {
            return false;
        };
        0 <= byte_offset && byte_offset + bytes <= range_bytes
    }

    pub(super) fn proves_loadable_region_from_range(
        &self,
        range_base: &Pointer,
        range_bytes: &Bitvector32Term,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        if range_base == base && range_bytes == bytes {
            return true;
        }

        if let Some(byte_width) = bytes.as_const()
            && self.proves_loadable_cell_from_region(range_base, range_bytes, base, byte_width)
        {
            return true;
        }

        if let Some(byte_offset) = pointer_byte_offset_from_base(base, range_base) {
            let access_end = Bitvector32Term::add(byte_offset.clone(), bytes.clone());
            return self.decide(&ConditionTerm::signed_greater_equal(
                byte_offset,
                Bitvector32Term::Constant(0),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_equal(
                    access_end,
                    range_bytes.clone(),
                )) == Some(true);
        }

        false
    }

    pub(super) fn proves_access_from_memory_block(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        let Some(block) = memory.blocks.get(&pointer.block) else {
            return false;
        };
        let base = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        self.proves_loadable_cell_from_region(
            &base,
            &Bitvector32Term::Constant(block.size()),
            pointer,
            byte_width,
        )
    }

    pub(super) fn proves_loadable_cell_from_region(
        &self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        if base.block != pointer.block {
            return false;
        }

        if byte_width == 4
            && let Some(index) = self.pointer_element_index_from_base(pointer, base)
            && let Some(element_count) = int32_element_count_from_bytes(bytes)
            && self.decide(&ConditionTerm::signed_greater_equal(
                index.clone(),
                Bitvector32Term::Constant(0),
            )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(index, element_count)) == Some(true)
        {
            return true;
        }

        if let Some(byte_offset) = pointer_byte_offset_from_base(pointer, base) {
            let access_end =
                Bitvector32Term::add(byte_offset.clone(), Bitvector32Term::Constant(byte_width));
            return self.decide(&ConditionTerm::signed_greater_equal(
                byte_offset,
                Bitvector32Term::Constant(0),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_equal(access_end, bytes.clone()))
                    == Some(true);
        }

        false
    }

    pub(super) fn pointers_proven_disjoint_by_range(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                self.pointer_in_range(left, left_base, left_start, left_end)
                    && self.pointer_in_range(right, right_base, right_start, right_end)
                    || self.pointer_in_range(right, left_base, left_start, left_end)
                        && self.pointer_in_range(left, right_base, right_start, right_end)
            }
            Proposition::CResourceSeparate {
                left: CResource::Memory(left_range),
                right: CResource::Memory(right_range),
            } => {
                self.pointer_in_range(
                    left,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                ) && self.pointer_in_range(
                    right,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                ) || self.pointer_in_range(
                    right,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                ) && self.pointer_in_range(
                    left,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                )
            }
            _ => false,
        }) || self.proves_resource_separate(
            &CResource::Memory(CMemoryRange::new(
                left.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &CResource::Memory(CMemoryRange::new(
                right.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
        )
    }

    pub(super) fn pointers_proven_disjoint_by_explicit_range_for_memory_resolution(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                pointer_in_range_for_memory_resolution(left, left_base, left_start, left_end, self)
                    && pointer_in_range_for_memory_resolution(
                        right,
                        right_base,
                        right_start,
                        right_end,
                        self,
                    )
                    || pointer_in_range_for_memory_resolution(
                        right, left_base, left_start, left_end, self,
                    ) && pointer_in_range_for_memory_resolution(
                        left,
                        right_base,
                        right_start,
                        right_end,
                        self,
                    )
            }
            Proposition::CResourceSeparate {
                left: CResource::Memory(left_range),
                right: CResource::Memory(right_range),
            } => {
                pointer_in_memory_range_for_memory_resolution(left, left_range, self)
                    && pointer_in_memory_range_for_memory_resolution(right, right_range, self)
                    || pointer_in_memory_range_for_memory_resolution(right, left_range, self)
                        && pointer_in_memory_range_for_memory_resolution(left, right_range, self)
            }
            _ => false,
        })
    }

    pub(super) fn memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
        &self,
        left: &CMemoryRange,
        right: &CMemoryRange,
    ) -> bool {
        // Prefer certificates where one queried range is structurally inside
        // one side. This gives the other side a single, directed equivalence
        // check instead of exploring both orientations of every separation
        // fact before reaching the structurally relevant certificate.
        if self.prop_facts.iter().any(|proposition| {
            let Proposition::CResourceSeparate {
                left: CResource::Memory(fact_left),
                right: CResource::Memory(fact_right),
            } = proposition
            else {
                return false;
            };
            memory_range_shallowly_contained(left, fact_left)
                && memory_range_contained_for_memory_resolution(right, fact_right, self)
                || memory_range_shallowly_contained(right, fact_right)
                    && memory_range_contained_for_memory_resolution(left, fact_left, self)
                || memory_range_shallowly_contained(right, fact_left)
                    && memory_range_contained_for_memory_resolution(left, fact_right, self)
                || memory_range_shallowly_contained(left, fact_right)
                    && memory_range_contained_for_memory_resolution(right, fact_left, self)
        }) {
            return true;
        }

        self.prop_facts.iter().any(|proposition| {
            let Proposition::CResourceSeparate {
                left: CResource::Memory(fact_left),
                right: CResource::Memory(fact_right),
            } = proposition
            else {
                return false;
            };
            memory_range_contained_for_memory_resolution(left, fact_left, self)
                && memory_range_contained_for_memory_resolution(right, fact_right, self)
                || memory_range_contained_for_memory_resolution(right, fact_left, self)
                    && memory_range_contained_for_memory_resolution(left, fact_right, self)
        })
    }

    fn pointer_element_index_from_base(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Bitvector32Term> {
        if pointer.block != base.block {
            return None;
        }
        if pointer.offset == base.offset {
            return Some(Bitvector32Term::Constant(0));
        }
        if self.decide(&ConditionTerm::pointer_offset_equal(
            pointer.offset.clone(),
            base.offset.clone(),
        )) == Some(true)
        {
            return Some(Bitvector32Term::Constant(0));
        }

        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if left.as_ref() == &base.offset
                || self.decide(&ConditionTerm::pointer_offset_equal(
                    left.as_ref().clone(),
                    base.offset.clone(),
                )) == Some(true)
            {
                return int32_element_index_from_offset(right);
            }
            if right.as_ref() == &base.offset
                || self.decide(&ConditionTerm::pointer_offset_equal(
                    right.as_ref().clone(),
                    base.offset.clone(),
                )) == Some(true)
            {
                return int32_element_index_from_offset(left);
            }
        }

        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            if &pointer.offset == left.as_ref()
                || self.decide(&ConditionTerm::pointer_offset_equal(
                    pointer.offset.clone(),
                    left.as_ref().clone(),
                )) == Some(true)
            {
                return int32_element_index_from_offset(right)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
            if &pointer.offset == right.as_ref()
                || self.decide(&ConditionTerm::pointer_offset_equal(
                    pointer.offset.clone(),
                    right.as_ref().clone(),
                )) == Some(true)
            {
                return int32_element_index_from_offset(left)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
        }

        pointer.element_index_from_base(base)
    }

    pub(super) fn pointer_in_range(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        let range_base = base.offset_by_int32_elements(start.clone());
        if let Some(index) = self.pointer_element_index_from_base(pointer, &range_base) {
            let range_length = Bitvector32Term::subtract(end.clone(), start.clone());
            if self.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                index.clone(),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_than(index, range_length)) == Some(true)
            {
                return true;
            }
        }

        let Some(index) = self.pointer_element_index_from_base(pointer, base) else {
            return false;
        };
        self.decide(&ConditionTerm::signed_less_equal(
            start.clone(),
            index.clone(),
        )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(index, end.clone())) == Some(true)
    }

    pub(super) fn proves_memory_disjoint(
        &self,
        left_base: &Pointer,
        left_start: &Bitvector32Term,
        left_end: &Bitvector32Term,
        right_base: &Pointer,
        right_start: &Bitvector32Term,
        right_end: &Bitvector32Term,
    ) -> bool {
        let left = CMemoryRange::new(left_base.clone(), left_start.clone(), left_end.clone());
        let right = CMemoryRange::new(right_base.clone(), right_start.clone(), right_end.clone());
        self.range_covered_by_disjoint_fact_ranges(&left, &right)
            || self.range_covered_by_disjoint_fact_ranges(&right, &left)
    }

    pub(super) fn proves_memory_disjoint_from_resource_separate(
        &self,
        left_base: &Pointer,
        left_start: &Bitvector32Term,
        left_end: &Bitvector32Term,
        right_base: &Pointer,
        right_start: &Bitvector32Term,
        right_end: &Bitvector32Term,
    ) -> bool {
        let left = CMemoryRange::new(left_base.clone(), left_start.clone(), left_end.clone());
        let right = CMemoryRange::new(right_base.clone(), right_start.clone(), right_end.clone());
        self.proves_resource_separate(
            &CResource::Memory(left.clone()),
            &CResource::Memory(right.clone()),
        ) || self.range_covered_by_resource_separate_ranges(&left, &right)
            || self.range_covered_by_resource_separate_ranges(&right, &left)
    }

    pub(super) fn proves_resource_contains(&self, parent: &CResource, child: &CResource) -> bool {
        if self.resource_contains_builtin(parent, child) {
            return true;
        }

        let mut seen = BTreeSet::new();
        let mut stack = vec![parent.clone()];
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            if self.resource_contains_builtin(&current, child) {
                return true;
            }
            for proposition in &self.prop_facts {
                let Proposition::CResourceContains {
                    parent: fact_parent,
                    child: fact_child,
                } = proposition
                else {
                    continue;
                };
                if self.resource_contains_builtin(&current, fact_parent) {
                    stack.push(fact_child.clone());
                }
            }
        }
        false
    }

    pub(super) fn proves_resource_separate(&self, left: &CResource, right: &CResource) -> bool {
        if self.prop_facts.iter().any(|proposition| {
            let Proposition::CResourceSeparate {
                left: fact_left,
                right: fact_right,
            } = proposition
            else {
                return false;
            };
            self.proves_resource_contains(fact_left, left)
                && self.proves_resource_contains(fact_right, right)
                || self.proves_resource_contains(fact_left, right)
                    && self.proves_resource_contains(fact_right, left)
        }) {
            return true;
        }

        if let (CResource::Memory(left), CResource::Memory(right)) = (left, right) {
            return self.range_covered_by_resource_separate_ranges(left, right)
                || self.range_covered_by_resource_separate_ranges(right, left);
        }

        false
    }

    fn resource_contains_builtin(&self, parent: &CResource, child: &CResource) -> bool {
        if parent == child {
            return true;
        }
        let (CResource::Memory(parent), CResource::Memory(child)) = (parent, child) else {
            return false;
        };
        if self.memory_ranges_proven_equal(parent, child) {
            return true;
        }
        if Bitvector32Term::subtract(child.end.clone(), child.start.clone()).as_const() == Some(1) {
            let child_pointer = child.base.offset_by_int32_elements(child.start.clone());
            return self.pointer_in_range(
                &child_pointer,
                parent.base(),
                parent.start(),
                parent.end(),
            );
        }
        self.range_covered_by_fact_range(child, parent.base(), parent.start(), parent.end())
    }

    fn memory_ranges_proven_equal(&self, left: &CMemoryRange, right: &CMemoryRange) -> bool {
        let left_length = memory_range_length_term(left);
        let right_length = memory_range_length_term(right);
        self.pointers_proven_equal_for_fact_transport(left.base(), right.base())
            && self.bitvector_terms_equal_for_fact_transport(left.start(), right.start())
            && self.bitvector_terms_equal_for_fact_transport(&left_length, &right_length)
    }

    fn pointers_proven_equal_for_fact_transport(&self, left: &Pointer, right: &Pointer) -> bool {
        if pointers_proven_equal(left, right, self) {
            return true;
        }
        if left.block != right.block {
            return false;
        }
        let (Some(left), Some(right)) = (
            int32_element_index_from_offset(&left.offset),
            int32_element_index_from_offset(&right.offset),
        ) else {
            return false;
        };
        self.bitvector_terms_equal_for_fact_transport(&left, &right)
    }

    fn bitvector_terms_equal_for_fact_transport(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        // Snapshot-aware endpoints are valid only for bounded fact transport.
        // Keeping them out of the global equality graph avoids recursive
        // memory resolution and changes to symbolic execution paths.
        if self.bitvector_terms_equal_for_transport(left, right)
            || self.bitvector_terms_equal_from_snapshot_facts(left, right)
        {
            return true;
        }

        match (left, right) {
            (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
            | (
                Bitvector32Term::Subtract(left_a, left_b),
                Bitvector32Term::Subtract(right_a, right_b),
            )
            | (
                Bitvector32Term::Multiply(left_a, left_b),
                Bitvector32Term::Multiply(right_a, right_b),
            ) => {
                self.bitvector_terms_equal_for_fact_transport(left_a, right_a)
                    && self.bitvector_terms_equal_for_fact_transport(left_b, right_b)
            }
            _ => false,
        }
    }

    fn bitvector_terms_equal_from_snapshot_facts(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let endpoint_matches = |left: &Bitvector32Term, right: &Bitvector32Term| {
            left == right || memory_load_terms_equal_for_fact_transport(left, right, self)
        };
        let mut seen = BTreeSet::new();
        let mut stack = vec![left.clone()];
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            if endpoint_matches(&term, right) {
                return true;
            }
            for (condition, value) in &self.condition_facts {
                if !*value {
                    continue;
                }
                let (fact_left, fact_right) = match condition {
                    ConditionTerm::Bitvector32Equal(fact_left, fact_right) => {
                        (fact_left.as_ref().clone(), fact_right.as_ref().clone())
                    }
                    ConditionTerm::PointerOffsetEqual(fact_left, fact_right) => {
                        let (Some(fact_left), Some(fact_right)) = (
                            int32_element_index_from_offset(fact_left),
                            int32_element_index_from_offset(fact_right),
                        ) else {
                            continue;
                        };
                        (fact_left, fact_right)
                    }
                    _ => continue,
                };
                if endpoint_matches(&fact_left, &term) {
                    stack.push(fact_right.clone());
                }
                if endpoint_matches(&fact_right, &term) {
                    stack.push(fact_left);
                }
            }
        }
        false
    }

    fn range_covered_by_resource_separate_ranges(
        &self,
        target: &CMemoryRange,
        other: &CMemoryRange,
    ) -> bool {
        let mut intervals = Vec::new();
        for proposition in &self.prop_facts {
            let Proposition::CResourceSeparate { left, right } = proposition else {
                continue;
            };

            if self.proves_resource_contains(right, &CResource::Memory(other.clone()))
                && let CResource::Memory(left) = left
                && let Some(interval) = self.fact_range_interval_on_target(
                    target,
                    left.base(),
                    left.start(),
                    left.end(),
                )
            {
                intervals.push(interval);
            }

            if self.proves_resource_contains(left, &CResource::Memory(other.clone()))
                && let CResource::Memory(right) = right
                && let Some(interval) = self.fact_range_interval_on_target(
                    target,
                    right.base(),
                    right.start(),
                    right.end(),
                )
            {
                intervals.push(interval);
            }
        }
        range_intervals_cover_target(target, intervals)
    }

    fn range_covered_by_disjoint_fact_ranges(
        &self,
        target: &CMemoryRange,
        other: &CMemoryRange,
    ) -> bool {
        let mut intervals = Vec::new();
        for proposition in &self.prop_facts {
            let Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } = proposition
            else {
                continue;
            };

            if self.range_covered_by_fact_range(other, right_base, right_start, right_end)
                && let Some(interval) =
                    self.fact_range_interval_on_target(target, left_base, left_start, left_end)
            {
                intervals.push(interval);
            }
            if self.range_covered_by_fact_range(other, left_base, left_start, left_end)
                && let Some(interval) =
                    self.fact_range_interval_on_target(target, right_base, right_start, right_end)
            {
                intervals.push(interval);
            }
        }
        range_intervals_cover_target(target, intervals)
    }

    fn fact_range_interval_on_target(
        &self,
        target: &CMemoryRange,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> Option<(i64, i64)> {
        if target.base.block != base.block {
            return None;
        }
        let base_delta = self.pointer_element_index_from_base(base, &target.base)?;
        let start = Bitvector32Term::add(base_delta.clone(), start.clone());
        let end = Bitvector32Term::add(base_delta, end.clone());
        Some((
            signed_bitvector_constant(&start)?,
            signed_bitvector_constant(&end)?,
        ))
    }

    pub(super) fn pointer_access_in_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        if byte_width == 4
            && let Some(index) = pointer.element_index_from_base(base)
            && self.decide(&ConditionTerm::signed_less_equal(
                start.clone(),
                index.clone(),
            )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(index, end.clone())) == Some(true)
        {
            return true;
        }

        if byte_width.is_multiple_of(4) {
            let range_base = base.offset_by_int32_elements(start.clone());
            let access_length = Bitvector32Term::Constant(byte_width / 4);
            if pointer == &range_base
                && end == &Bitvector32Term::add(start.clone(), access_length.clone())
            {
                return true;
            }
            if let Some(index) = self.pointer_element_index_from_base(pointer, &range_base) {
                let range_length = Bitvector32Term::subtract(end.clone(), start.clone());
                let access_end = Bitvector32Term::add(index.clone(), access_length);
                if self.decide(&ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    index,
                )) == Some(true)
                    && self.decide(&ConditionTerm::signed_less_equal(access_end, range_length))
                        == Some(true)
                {
                    return true;
                }
            }
        }

        if let Some(index) = self.pointer_element_index_from_base(pointer, base) {
            if byte_width == 4 {
                return self.decide(&ConditionTerm::signed_less_equal(
                    start.clone(),
                    index.clone(),
                )) == Some(true)
                    && self.decide(&ConditionTerm::signed_less_than(index, end.clone()))
                        == Some(true);
            }
            if byte_width > 4 && byte_width.is_multiple_of(4) {
                let element_width = Bitvector32Term::Constant(byte_width / 4);
                let access_end = Bitvector32Term::add(index.clone(), element_width);
                return self.decide(&ConditionTerm::signed_less_equal(start.clone(), index))
                    == Some(true)
                    && self.decide(&ConditionTerm::signed_less_equal(access_end, end.clone()))
                        == Some(true);
            }
        }

        if byte_width == 1 {
            let Some(index) = pointer_byte_offset_from_base(pointer, base) else {
                return false;
            };
            return self.decide(&ConditionTerm::signed_less_equal(
                start.clone(),
                index.clone(),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_than(index, end.clone())) == Some(true);
        }

        false
    }

    pub(super) fn ranges_proven_disjoint_from_pointer(
        &self,
        ranges: &[CMemoryRange],
        pointer: &Pointer,
    ) -> bool {
        ranges
            .iter()
            .all(|range| self.range_proven_disjoint_from_pointer(range, pointer))
    }

    pub(super) fn ranges_directly_disjoint_from_pointer(
        &self,
        ranges: &[CMemoryRange],
        pointer: &Pointer,
    ) -> bool {
        ranges.iter().all(|range| {
            if range.base.blocks_proven_distinct(pointer) {
                return true;
            }
            if pointer_in_memory_range_shallow(pointer, range) {
                return false;
            }
            let direct_index = self.direct_pointer_element_index_from_base(pointer, &range.base);
            if let Some(index) = direct_index.as_ref()
                && let (Some(index), Some(start), Some(end)) = (
                    signed_bitvector_constant(index),
                    signed_bitvector_constant(&range.start),
                    signed_bitvector_constant(&range.end),
                )
            {
                return index < start || end <= index;
            }
            if self.prop_facts.iter().any(|proposition| match proposition {
                Proposition::CMemoryDisjoint {
                    left_base,
                    left_start,
                    left_end,
                    right_base,
                    right_start,
                    right_end,
                } => {
                    memory_range_shallowly_contained_in_parts(
                        range, left_base, left_start, left_end,
                    ) && pointer_in_range_shallow(pointer, right_base, right_start, right_end)
                        || memory_range_shallowly_contained_in_parts(
                            range,
                            right_base,
                            right_start,
                            right_end,
                        ) && pointer_in_range_shallow(pointer, left_base, left_start, left_end)
                }
                Proposition::CResourceSeparate {
                    left: CResource::Memory(left_range),
                    right: CResource::Memory(right_range),
                } => {
                    memory_range_shallowly_contained(range, left_range)
                        && (pointer_in_memory_range_shallow(pointer, right_range)
                            || self.pointer_directly_in_memory_range(pointer, right_range))
                        || memory_range_shallowly_contained(range, right_range)
                            && (pointer_in_memory_range_shallow(pointer, left_range)
                                || self.pointer_directly_in_memory_range(pointer, left_range))
                        || pointer_in_memory_range_shallow(pointer, left_range)
                            && memory_range_contained_for_memory_resolution(
                                range,
                                right_range,
                                self,
                            )
                        || pointer_in_memory_range_shallow(pointer, right_range)
                            && memory_range_contained_for_memory_resolution(range, left_range, self)
                        || self.pointer_directly_in_memory_range(pointer, left_range)
                            && memory_range_contained_for_memory_resolution(
                                range,
                                right_range,
                                self,
                            )
                        || self.pointer_directly_in_memory_range(pointer, right_range)
                            && memory_range_contained_for_memory_resolution(range, left_range, self)
                }
                _ => false,
            }) {
                return true;
            }

            let Some(index) = direct_index else {
                return false;
            };
            bitvector_index_outside_range_shallow(&index, &range.start, &range.end, self)
        })
    }

    fn direct_pointer_element_index_from_base(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Bitvector32Term> {
        if pointer.block != base.block {
            return None;
        }
        let offsets_equal = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            if left == right {
                return true;
            }
            match (left, right) {
                (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width: left_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: right,
                        byte_width: right_width,
                    },
                ) => {
                    left_width == right_width && self.bitvector_terms_equal_from_facts(left, right)
                }
                _ => false,
            }
        };
        if offsets_equal(&pointer.offset, &base.offset) {
            return Some(Bitvector32Term::Constant(0));
        }
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if offsets_equal(left, &base.offset) {
                return int32_element_index_from_offset(right);
            }
            if offsets_equal(right, &base.offset) {
                return int32_element_index_from_offset(left);
            }
        }
        pointer.element_index_from_base(base)
    }

    fn pointer_directly_in_memory_range(&self, pointer: &Pointer, range: &CMemoryRange) -> bool {
        let Some(index) = self.direct_pointer_element_index_from_base(pointer, &range.base) else {
            return false;
        };
        if let (Some(index), Some(start), Some(end)) = (
            signed_bitvector_constant(&index),
            signed_bitvector_constant(&range.start),
            signed_bitvector_constant(&range.end),
        ) {
            return start <= index && index < end;
        }
        bitvector_index_in_range_shallow(&index, &range.start, &range.end, self)
    }

    fn range_proven_disjoint_from_pointer(&self, range: &CMemoryRange, pointer: &Pointer) -> bool {
        if range.base.blocks_proven_distinct(pointer) {
            return true;
        }
        if pointer_in_memory_range_shallow(pointer, range) {
            return false;
        }

        if self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                memory_range_shallowly_contained_in_parts(range, left_base, left_start, left_end)
                    && pointer_in_range_shallow(pointer, right_base, right_start, right_end)
                    || memory_range_shallowly_contained_in_parts(
                        range,
                        right_base,
                        right_start,
                        right_end,
                    ) && pointer_in_range_shallow(pointer, left_base, left_start, left_end)
            }
            Proposition::CResourceSeparate {
                left: CResource::Memory(left_range),
                right: CResource::Memory(right_range),
            } => {
                memory_range_shallowly_contained(range, left_range)
                    && pointer_in_memory_range_shallow(pointer, right_range)
                    || memory_range_shallowly_contained(range, right_range)
                        && pointer_in_memory_range_shallow(pointer, left_range)
            }
            _ => false,
        }) {
            return true;
        }

        let pointer_range = CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        if self.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            range,
            &pointer_range,
        ) {
            return true;
        }

        if let PointerOffsetTerm::Add(left, right) = &range.base.offset {
            let forward_offset = if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                left.as_ref().clone(),
            )) == Some(true)
            {
                int32_element_index_from_offset(right)
            } else if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                right.as_ref().clone(),
            )) == Some(true)
            {
                int32_element_index_from_offset(left)
            } else {
                None
            };
            if let Some(forward_offset) = forward_offset {
                let range_start = Bitvector32Term::add(forward_offset, range.start.clone());
                if self.decide(&ConditionTerm::signed_less_than(
                    Bitvector32Term::Constant(0),
                    range_start,
                )) == Some(true)
                {
                    return true;
                }
            }
        }

        if let Some(index) = self.direct_pointer_element_index_from_base(pointer, &range.base) {
            if let (Some(index), Some(start), Some(end)) = (
                signed_bitvector_constant(&index),
                signed_bitvector_constant(&range.start),
                signed_bitvector_constant(&range.end),
            ) && (index < start || end <= index)
            {
                return true;
            }
            if self.decide(&ConditionTerm::signed_less_than(
                index.clone(),
                range.start.clone(),
            )) == Some(true)
                || self.decide(&ConditionTerm::signed_less_equal(range.end.clone(), index))
                    == Some(true)
            {
                return true;
            }
        }

        self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } = proposition
            else {
                return false;
            };

            self.range_covered_by_fact_range(range, left_base, left_start, left_end)
                && self.pointer_in_range(pointer, right_base, right_start, right_end)
                || self.range_covered_by_fact_range(range, right_base, right_start, right_end)
                    && self.pointer_in_range(pointer, left_base, left_start, left_end)
        })
    }

    pub(super) fn range_covered_by_fact_range(
        &self,
        range: &CMemoryRange,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        if &range.base == base {
            let base_delta = relative_range_offset(range.start(), start);
            let range_length =
                Bitvector32Term::subtract(range.end().clone(), range.start().clone());
            let fact_length = Bitvector32Term::subtract(end.clone(), start.clone());
            let end_is_covered = if range_length == Bitvector32Term::Constant(1) {
                self.decide(&ConditionTerm::signed_less_than(
                    base_delta.clone(),
                    fact_length.clone(),
                )) == Some(true)
            } else {
                let range_end = Bitvector32Term::add(base_delta.clone(), range_length);
                self.decide(&ConditionTerm::signed_less_equal(range_end, fact_length)) == Some(true)
            };
            if self.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                base_delta,
            )) == Some(true)
                && end_is_covered
            {
                return true;
            }
        }

        let fact_base = base.offset_by_int32_elements(start.clone());
        let range_base = range.base.offset_by_int32_elements(range.start.clone());
        if let Some(base_delta) = self.pointer_element_index_from_base(&range_base, &fact_base) {
            let range_length = Bitvector32Term::subtract(range.end.clone(), range.start.clone());
            let fact_length = Bitvector32Term::subtract(end.clone(), start.clone());
            let range_end = Bitvector32Term::add(base_delta.clone(), range_length);
            if self.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                base_delta,
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_equal(range_end, fact_length))
                    == Some(true)
            {
                return true;
            }
        }

        let Some(base_delta) = self.pointer_element_index_from_base(&range.base, base) else {
            return false;
        };
        let range_start = Bitvector32Term::add(base_delta.clone(), range.start.clone());
        let range_end = Bitvector32Term::add(base_delta, range.end.clone());

        self.decide(&ConditionTerm::signed_less_equal(
            start.clone(),
            range_start,
        )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_equal(range_end, end.clone())) == Some(true)
    }
}

fn proposition_derivation(
    conclusion: &Proposition,
    rule: PropositionDerivationRule,
) -> PropositionDerivation {
    PropositionDerivation {
        conclusion: conclusion.clone(),
        rule,
    }
}

impl PropositionDerivation {
    /// Check this proof tree against an available context without searching for
    /// alternate proofs.
    pub fn replay(&self, available: &Assumptions) -> bool {
        match &self.rule {
            PropositionDerivationRule::ContextFree => solve_builtin_prop(&self.conclusion),
            PropositionDerivationRule::ContextualAtomic { premises, for_simp } => {
                available.includes(premises)
                    && premises.proves_atomic_for_derivation(&self.conclusion, *for_simp)
            }
            PropositionDerivationRule::Explosion { premises } => {
                available.includes(premises) && premises.is_inconsistent()
            }
            PropositionDerivationRule::And { left, right } => {
                let Proposition::And(expected_left, expected_right) = &self.conclusion else {
                    return false;
                };
                left.conclusion == **expected_left
                    && right.conclusion == **expected_right
                    && left.replay(available)
                    && right.replay(available)
            }
            PropositionDerivationRule::OrLeft(proof) => {
                let Proposition::Or(expected, _) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **expected && proof.replay(available)
            }
            PropositionDerivationRule::OrRight(proof) => {
                let Proposition::Or(_, expected) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **expected && proof.replay(available)
            }
            PropositionDerivationRule::DoubleNegation(proof) => {
                let Proposition::Not(body) = &self.conclusion else {
                    return false;
                };
                let Proposition::Not(expected) = body.as_ref() else {
                    return false;
                };
                proof.conclusion == **expected && proof.replay(available)
            }
            PropositionDerivationRule::Implies { antecedent, body } => {
                let Proposition::Implies(expected_antecedent, expected_body) = &self.conclusion
                else {
                    return false;
                };
                antecedent == expected_antecedent.as_ref()
                    && body.conclusion == **expected_body
                    && body.replay(&available.clone().assume_proposition(antecedent.clone()))
            }
            PropositionDerivationRule::ImpliesFalseAntecedent(proof) => {
                let Proposition::Implies(expected_antecedent, _) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == Proposition::Not(Box::new(expected_antecedent.as_ref().clone()))
                    && proof.replay(available)
            }
            PropositionDerivationRule::ForAllBody(proof) => {
                let Proposition::ForAll { body, .. } = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **body && proof.replay(available)
            }
            PropositionDerivationRule::FiniteForAll { instances } => {
                let expected = available.finite_forall_instantiations(&self.conclusion);
                !expected.is_empty()
                    && derivations_match_propositions(instances, &expected)
                    && instances.iter().all(|proof| proof.replay(available))
            }
            PropositionDerivationRule::FiniteContextSplit {
                variable,
                lower,
                upper,
                instances,
            } => {
                let Some(range) = available.finite_context_range(*variable) else {
                    return false;
                };
                if range.lower < *lower || range.upper > *upper {
                    return false;
                }
                let Ok(width) = usize::try_from(upper - lower + 1) else {
                    return false;
                };
                if width > FINITE_CONTEXT_SPLIT_LIMIT {
                    return false;
                }
                let expected = (*lower..=*upper)
                    .map(|value| {
                        substitute_bitvector_variable_in_proposition(
                            &self.conclusion,
                            *variable,
                            &signed_i64_bitvector_constant(value),
                        )
                    })
                    .collect::<Vec<_>>();
                derivations_match_propositions(instances, &expected)
                    && instances.iter().all(|proof| proof.replay(available))
            }
            PropositionDerivationRule::DisjunctionCases { disjunction, cases } => {
                if !matches!(self.conclusion, Proposition::Or(_, _))
                    || !available.prop_facts.contains(disjunction)
                {
                    return false;
                }
                let mut expected_cases = Vec::new();
                collect_or_cases(disjunction, &mut expected_cases);
                if expected_cases.len() < 2
                    || expected_cases.len() > DISJUNCTION_CASE_LIMIT
                    || cases.len() != expected_cases.len()
                {
                    return false;
                }
                let mut base = available.clone();
                base.prop_facts.remove(disjunction);
                cases.iter().zip(expected_cases).all(|(proof, case)| {
                    proof.conclusion == self.conclusion
                        && proof.replay(&base.clone().assume_proposition(case))
                })
            }
        }
    }
}

fn derivations_match_propositions(
    derivations: &[PropositionDerivation],
    propositions: &[Proposition],
) -> bool {
    derivations.len() == propositions.len()
        && derivations
            .iter()
            .zip(propositions)
            .all(|(derivation, proposition)| derivation.conclusion == *proposition)
}

fn relative_range_offset(value: &Bitvector32Term, origin: &Bitvector32Term) -> Bitvector32Term {
    match (value, origin) {
        (
            Bitvector32Term::Subtract(value, value_origin),
            Bitvector32Term::Subtract(origin, origin_origin),
        ) if value_origin == origin_origin => {
            Bitvector32Term::subtract(value.as_ref().clone(), origin.as_ref().clone())
        }
        _ => Bitvector32Term::subtract(value.clone(), origin.clone()),
    }
}

fn signed_int_min_term() -> Bitvector32Term {
    Bitvector32Term::Constant(i32::MIN as u32)
}

fn signed_int_max_term() -> Bitvector32Term {
    Bitvector32Term::Constant(i32::MAX as u32)
}

fn range_intervals_cover_target(target: &CMemoryRange, mut intervals: Vec<(i64, i64)>) -> bool {
    let Some(target_start) = signed_bitvector_constant(target.start()) else {
        return false;
    };
    let Some(target_end) = signed_bitvector_constant(target.end()) else {
        return false;
    };
    if target_end <= target_start {
        return true;
    }

    intervals.sort_unstable();
    let mut covered_until = target_start;
    for (start, end) in intervals {
        let start = start.max(target_start);
        let end = end.min(target_end);
        if end <= covered_until {
            continue;
        }
        if start > covered_until {
            return false;
        }
        covered_until = end;
        if covered_until >= target_end {
            return true;
        }
    }
    false
}

fn memory_range_length_term(range: &CMemoryRange) -> Bitvector32Term {
    match range.end() {
        Bitvector32Term::Add(base, length) if base.as_ref() == range.start() => {
            length.as_ref().clone()
        }
        Bitvector32Term::Add(length, base) if base.as_ref() == range.start() => {
            length.as_ref().clone()
        }
        end => Bitvector32Term::subtract(end.clone(), range.start().clone()),
    }
}

fn memory_range_shallowly_contained_in_parts(
    range: &CMemoryRange,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
) -> bool {
    memory_range_shallowly_contained(
        range,
        &CMemoryRange::new(base.clone(), start.clone(), end.clone()),
    )
}

fn memory_range_shallowly_contained(range: &CMemoryRange, parent: &CMemoryRange) -> bool {
    let Some(base_index) = range.base().element_index_from_base(parent.base()) else {
        return false;
    };
    let range_start = Bitvector32Term::add(base_index.clone(), range.start().clone());
    let range_end = Bitvector32Term::add(base_index, range.end().clone());
    affine_bitvector_difference_constant(&range_start, parent.start())
        .is_some_and(|delta| delta >= 0)
        && affine_bitvector_difference_constant(parent.end(), &range_end)
            .is_some_and(|delta| delta >= 0)
}

fn memory_range_contained_for_memory_resolution(
    range: &CMemoryRange,
    parent: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    if memory_range_shallowly_contained(range, parent) {
        return true;
    }

    if pointers_proven_equal_for_memory_resolution(range.base(), parent.base(), assumptions) {
        return exact_less_equal_for_memory_resolution(parent.start(), range.start(), assumptions)
            && exact_less_equal_for_memory_resolution(range.end(), parent.end(), assumptions);
    }

    if affine_bitvector_difference_constant(range.end(), range.start()) == Some(1) {
        let pointer = range.base().offset_by_int32_elements(range.start().clone());
        if pointer_in_memory_range_for_memory_resolution(&pointer, parent, assumptions) {
            return true;
        }
    }

    false
}

fn exact_less_equal_for_memory_resolution(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if let (Some(left), Some(right)) = (
        signed_bitvector_constant(left),
        signed_bitvector_constant(right),
    ) {
        return left <= right;
    }
    if left == right
        || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        || assumptions.exact_condition_value(&ConditionTerm::signed_less_equal(
            left.clone(),
            right.clone(),
        )) == Some(true)
        || assumptions.has_exact_order_path(left, right, false)
    {
        return true;
    }
    if assumptions
        .condition_facts
        .iter()
        .any(|(condition, value)| {
            if !*value {
                return false;
            }
            let (fact_left, fact_right) = match condition {
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right)
                | ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right) => {
                    (fact_left.as_ref(), fact_right.as_ref())
                }
                _ => return false,
            };
            bitvector_terms_proven_equal_for_memory_resolution(fact_left, left, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(
                    fact_right,
                    right,
                    assumptions,
                )
        })
    {
        return true;
    }
    let Some(left_constant) = signed_bitvector_constant(left) else {
        return false;
    };
    assumptions
        .condition_facts
        .iter()
        .any(|(condition, value)| {
            if !*value {
                return false;
            }
            let (fact_left, fact_right, strict) = match condition {
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right) => {
                    (fact_left.as_ref(), fact_right.as_ref(), false)
                }
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right) => {
                    (fact_left.as_ref(), fact_right.as_ref(), true)
                }
                _ => return false,
            };
            signed_bitvector_constant(fact_left)
                .is_some_and(|bound| left_constant <= if strict { bound + 1 } else { bound })
                && (fact_right == right
                    || bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        right,
                        assumptions,
                    ))
        })
}

fn pointer_in_memory_range_shallow(pointer: &Pointer, range: &CMemoryRange) -> bool {
    pointer_in_range_shallow(pointer, range.base(), range.start(), range.end())
}

fn pointer_in_memory_range_for_memory_resolution(
    pointer: &Pointer,
    range: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    pointer_in_range_for_memory_resolution(
        pointer,
        range.base(),
        range.start(),
        range.end(),
        assumptions,
    )
}

fn pointer_in_range_for_memory_resolution(
    pointer: &Pointer,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if pointer.block != base.block {
        return false;
    }
    let mut indexes = pointer
        .element_index_from_base(base)
        .into_iter()
        .collect::<Vec<_>>();
    if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
        if pointer_offsets_proven_equal_for_memory_resolution(left, &base.offset, assumptions)
            && let Some(index) = int32_element_index_from_offset(right)
            && !indexes.contains(&index)
        {
            indexes.push(index);
        }
        if pointer_offsets_proven_equal_for_memory_resolution(right, &base.offset, assumptions)
            && let Some(index) = int32_element_index_from_offset(left)
            && !indexes.contains(&index)
        {
            indexes.push(index);
        }
    }
    indexes
        .iter()
        .any(|index| bitvector_index_in_range_shallow(index, start, end, assumptions))
}

fn bitvector_index_in_range_shallow(
    index: &Bitvector32Term,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if let (Some(index), Some(start), Some(end)) = (
        signed_bitvector_constant(index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return start <= index && index < end;
    }
    let lower_bound_is_exact = assumptions.exact_condition_value(
        &ConditionTerm::signed_less_equal(start.clone(), index.clone()),
    ) == Some(true)
        || assumptions.has_exact_order_path(start, index, false)
        || start == &Bitvector32Term::Constant(0)
            && index.add_const_parts().is_some_and(|(base, increment)| {
                (increment as i32) > 0
                    && assumptions.has_exact_order_path(start, &base, false)
                    && (assumptions.exact_condition_value(&ConditionTerm::signed_add_overflows(
                        base.clone(),
                        Bitvector32Term::Constant(increment),
                    )) == Some(false)
                        || assumptions.exact_condition_value(&ConditionTerm::signed_add_overflows(
                            Bitvector32Term::Constant(increment),
                            base,
                        )) == Some(false))
            });
    let upper_bound_is_exact = assumptions
        .exact_condition_value(&ConditionTerm::signed_less_than(index.clone(), end.clone()))
        == Some(true)
        || assumptions.has_exact_order_path(index, end, true);
    if lower_bound_is_exact && upper_bound_is_exact {
        return true;
    }

    let (Some(offset), Some(length)) = (
        affine_bitvector_difference_constant(&index, start),
        affine_bitvector_difference_constant(end, start),
    ) else {
        return false;
    };
    0 <= offset && offset < length
}

fn bitvector_index_outside_range_shallow(
    index: &Bitvector32Term,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if let (Some(index), Some(start), Some(end)) = (
        signed_bitvector_constant(index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return index < start || end <= index;
    }
    if assumptions
        .exact_condition_value(&ConditionTerm::signed_less_than(
            index.clone(),
            start.clone(),
        ))
        == Some(true)
        || assumptions.has_exact_order_path(index, start, true)
        || assumptions
            .exact_condition_value(&ConditionTerm::signed_less_equal(
                end.clone(),
                index.clone(),
            ))
            == Some(true)
        || assumptions.has_exact_order_path(end, index, false)
    {
        return true;
    }
    affine_bitvector_difference_constant(index, start).is_some_and(|offset| offset < 0)
        || affine_bitvector_difference_constant(index, end).is_some_and(|offset| 0 <= offset)
}

fn pointer_in_range_shallow(
    pointer: &Pointer,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
) -> bool {
    let Some(index) = pointer.element_index_from_base(base) else {
        return false;
    };
    if let (Some(index), Some(start), Some(end)) = (
        signed_bitvector_constant(&index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return start <= index && index < end;
    }

    let (Some(offset), Some(length)) = (
        affine_bitvector_difference_constant(&index, start),
        affine_bitvector_difference_constant(end, start),
    ) else {
        return false;
    };
    0 <= offset && offset < length
}

fn affine_bitvector_difference_constant(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<i64> {
    let mut terms = BTreeMap::new();
    let mut constant = 0i64;
    collect_affine_bitvector_terms(left, 1, &mut terms, &mut constant)?;
    collect_affine_bitvector_terms(right, -1, &mut terms, &mut constant)?;
    terms.retain(|_, coefficient| *coefficient != 0);
    terms.is_empty().then_some(constant)
}

fn collect_affine_bitvector_terms(
    term: &Bitvector32Term,
    coefficient: i64,
    terms: &mut BTreeMap<Bitvector32Term, i64>,
    constant: &mut i64,
) -> Option<()> {
    match term {
        Bitvector32Term::Constant(value) => {
            *constant = constant.checked_add(coefficient.checked_mul(i64::from(*value as i32))?)?;
        }
        Bitvector32Term::Add(left, right) => {
            collect_affine_bitvector_terms(left, coefficient, terms, constant)?;
            collect_affine_bitvector_terms(right, coefficient, terms, constant)?;
        }
        Bitvector32Term::Subtract(left, right) => {
            collect_affine_bitvector_terms(left, coefficient, terms, constant)?;
            collect_affine_bitvector_terms(right, coefficient.checked_neg()?, terms, constant)?;
        }
        atom => {
            let current = terms.entry(atom.clone()).or_default();
            *current = current.checked_add(coefficient)?;
        }
    }
    Some(())
}

impl ProofObligation {
    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            context: None,
            assumable: true,
        }
    }

    pub fn verification_condition(proposition: Proposition) -> Self {
        Self {
            proposition,
            context: None,
            assumable: false,
        }
    }

    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    pub fn is_assumable(&self) -> bool {
        self.assumable
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::ConditionIs(condition, value))
    }

    pub fn memory_loadable(memory: CMemory, pointer: Pointer) -> Self {
        Self::memory_loadable_bytes(memory, pointer, 4)
    }

    pub fn memory_loadable_bytes(memory: CMemory, pointer: Pointer, byte_width: u32) -> Self {
        Self::new(Proposition::CMemoryLoadable {
            memory,
            base: pointer,
            bytes: Bitvector32Term::Constant(byte_width),
        })
    }

    pub fn memory_can_store(memory: CMemory, pointer: Pointer) -> Self {
        Self::memory_can_store_bytes(memory, pointer, 4)
    }

    pub fn memory_can_store_bytes(memory: CMemory, pointer: Pointer, byte_width: u32) -> Self {
        Self::new(Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        })
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }

    pub(super) fn map_proposition(self, f: impl FnOnce(Proposition) -> Proposition) -> Self {
        Self {
            proposition: f(self.proposition),
            context: self.context,
            assumable: self.assumable,
        }
    }
}

impl ExecutionPureFact {
    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: true,
            certified: false,
        }
    }

    pub(super) fn internal(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: false,
            certified: false,
        }
    }

    pub(super) fn certified(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: true,
            certified: true,
        }
    }

    pub(super) fn into_certified(mut self) -> Self {
        self.certified = true;
        self
    }

    pub(crate) fn with_proposition(mut self, proposition: Proposition) -> Self {
        self.proposition = proposition;
        self
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::ConditionIs(condition, value))
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub(super) fn is_public(&self) -> bool {
        self.public
    }

    pub(crate) fn is_certified(&self) -> bool {
        self.certified
    }
}

impl SymbolicCExecution {
    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicCExecutionPath {
    pub fn facts(&self) -> &[ExecutionPureFact] {
        &self.facts
    }

    pub fn execution_facts(&self) -> Vec<ExecutionPureFact> {
        let mut facts = self.facts.clone();
        for fact in &self.effect_facts {
            if !facts.contains(fact) {
                facts.push(fact.clone());
            }
        }
        facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

impl SymbolicCConditionEvaluation {
    pub fn paths(&self) -> &[SymbolicCConditionEvaluationPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicCConditionEvaluationPath {
    pub fn facts(&self) -> &[ExecutionPureFact] {
        &self.facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}
