//! Smart closure through a definedness-guarded comparison.
//!
//! Lowering a partial C expression such as `old(st.live) + result` at a call
//! or a return keeps its no-overflow condition as the antecedent of the
//! equality it states: `defined(old(st.live) + result) implies st.live ==
//! old(st.live) + result`. The kernel does not harvest such a consequent on
//! its own; the checked `extract` rule does once the guard is an available
//! fact. This closer selects the guarded comparisons whose consequent shares
//! an operand with the goal, proves each guard with an ordinary nested
//! `simp` (the bounded overflow-interval reasoning decides it from the
//! operands' bounds), extracts the consequent, and continues the closure.
//! Expansion therefore renders the discharge as `have defined(..) by { .. }`
//! followed by `extract(..)`. An implication under an ordinary condition is
//! not selected: applying it stays an explicit step.

use super::*;
use std::cell::Cell;

/// At most this many guarded comparisons are tried for one goal.
const MAX_GUARDED_CANDIDATES: usize = 6;

/// Nested guarded extractions (a guard, or the goal left after one
/// extraction, that itself needs another guarded equality) stop at this
/// depth, so the search stays bounded by the candidates tried per level.
const MAX_GUARDED_DEPTH: usize = 3;

thread_local! {
    static GUARDED_CONSEQUENT_DEPTH: Cell<usize> = const { Cell::new(0) };
}

struct GuardedConsequentScope;

impl GuardedConsequentScope {
    fn enter() -> Option<Self> {
        GUARDED_CONSEQUENT_DEPTH.with(|depth| {
            (depth.get() < MAX_GUARDED_DEPTH).then(|| {
                depth.set(depth.get() + 1);
                GuardedConsequentScope
            })
        })
    }
}

impl Drop for GuardedConsequentScope {
    fn drop(&mut self) {
        GUARDED_CONSEQUENT_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

impl<'a> Proof<'a> {
    pub(super) fn try_guarded_consequent_closure(&self) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        if !matches!(goal, Proposition::ConditionIs(..)) {
            return Ok(None);
        }
        let candidates = self.facts().guarded_implications_mentioning(goal);
        if candidates.is_empty() {
            return Ok(None);
        }
        let Some(_scope) = GuardedConsequentScope::enter() else {
            return Ok(None);
        };
        for implication in candidates.into_iter().take(MAX_GUARDED_CANDIDATES) {
            let Proposition::Implies(guard, consequent) = &implication else {
                continue;
            };
            if self.facts().contains(consequent) || self.antecedent_is_refuted(guard) {
                continue;
            }
            let Some((surface_guard, surface_consequent)) =
                self.guarded_implication_surfaces(guard, consequent)
            else {
                continue;
            };
            let Some(with_guard) = self.prove_guard(&surface_guard)? else {
                continue;
            };
            let Some(extracted) = attempt::candidate_outcome(
                with_guard.apply_step(ProofStep::Extract(surface_consequent.clone())),
            )?
            else {
                continue;
            };
            if extracted.is_complete() || extracted.focused_discharged() {
                return Ok(Some(extracted));
            }
            // An equality consequent names a goal operand: rewriting the goal
            // with it leaves the operands' own facts to close what remains.
            if matches!(
                consequent.as_ref(),
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(..) | ConditionTerm::Bitvector64Equal(..),
                    true
                )
            ) && let Some(rewritten) = attempt::candidate_outcome(
                extracted.apply_step(ProofStep::Rewrite(surface_consequent.clone())),
            )? {
                if rewritten.focused_discharged() {
                    return Ok(Some(rewritten));
                }
                if let Some(closed) = rewritten.try_simp_closure()? {
                    return Ok(Some(closed));
                }
            }
            if let Some(closed) = extracted.try_simp_closure()? {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// The `simp() using { .. }` form: a listed guarded equality whose guard
    /// the list does not state.
    pub(super) fn try_restricted_guarded_consequent(
        &self,
        surfaces: &[ClickProposition],
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
            let Proposition::Implies(guard, consequent) = kernel else {
                continue;
            };
            let ClickProposition::Implies(surface_guard, surface_consequent) = surface else {
                continue;
            };
            if !crate::kernel::proof::is_definedness_guard(guard)
                || premise_pairs
                    .iter()
                    .any(|(listed, _)| listed == guard.as_ref())
                || !matches!(consequent.as_ref(), Proposition::ConditionIs(..))
            {
                continue;
            }
            let others = surfaces
                .iter()
                .enumerate()
                .filter(|(other, _)| *other != index)
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>();
            let scope = self.begin_have(surface_guard.as_ref().clone()).ok()?;
            // The guard is a side condition of the listed fact: prefer the
            // other listed premises, and otherwise decide it as `simp` would.
            let proved = if others.is_empty() {
                None
            } else {
                scope.try_restricted_simp_closure(&others)
            }
            .or_else(|| scope.try_simp_closure().ok().flatten());
            let Some(proved) = proved else {
                continue;
            };
            let with_guard = proved.join().ok()?;
            let extracted = with_guard
                .apply_step(ProofStep::Extract(surface_consequent.as_ref().clone()))
                .ok()?;
            if extracted.focused_discharged() {
                return Some(extracted);
            }
            let mut remaining = others;
            remaining.push(surface_consequent.as_ref().clone());
            return extracted.try_restricted_simp_closure(&remaining);
        }
        None
    }

    /// Whether the kernel's own decision already refutes one conjunct of an
    /// antecedent, so proving it would be a search bound to fail (the other
    /// outcome's `result == 0 implies ..` on a path where `result == 1`).
    fn antecedent_is_refuted(&self, antecedent: &Proposition) -> bool {
        let mut pending = vec![antecedent];
        while let Some(proposition) = pending.pop() {
            match proposition {
                Proposition::And(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                Proposition::ConditionIs(condition, value)
                    if self
                        .facts()
                        .assumptions()
                        .decide(condition)
                        .is_some_and(|decided| decided != *value) =>
                {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    /// `have <guard> by { simp(); }`, or the proof unchanged when the guard
    /// is already available.
    fn prove_guard(&self, surface_guard: &ClickProposition) -> Result<Option<Self>, ClickError> {
        let Some(scope) = attempt::candidate_outcome(self.begin_have(surface_guard.clone()))?
        else {
            return Ok(None);
        };
        let Some(proved) = scope.try_simp_closure()? else {
            return Ok(None);
        };
        attempt::candidate_outcome(proved.join())
    }

    /// Spell the guard and the consequent of one selected guarded equality
    /// so each lowers back to exactly its kernel form. Terms read from the
    /// model fields the goal names are spelled through those fields at the
    /// current state, the function entry, or a recorded snapshot; other terms
    /// take the ordinary bounded synthesis. A candidate that does not lower
    /// back to its kernel form is not offered.
    fn guarded_implication_surfaces(
        &self,
        guard: &Proposition,
        consequent: &Proposition,
    ) -> Option<(ClickProposition, ClickProposition)> {
        let view = self
            .outcome_fixed_state_view()
            .or_else(|| self.execution_fixed_state_view())?;
        let mut accesses = Vec::new();
        if let Some(surface_goal) = self.surface_goal() {
            collect_goal_field_accesses(surface_goal, &mut accesses);
        }
        let bound = self
            .proposition_obligation()
            .map(|goal| {
                goal.surface_bindings
                    .iter()
                    .filter_map(|(name, binding)| match binding {
                        ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                            Bitvector32Term::Variable(variable),
                        ))) => Some((*variable, name.clone())),
                        _ => None,
                    })
                    .collect::<BTreeMap<_, _>>()
            })
            .unwrap_or_default();
        let speller = GuardedTermSpeller {
            view: &view,
            accesses: &accesses,
            snapshots: view.recorded_snapshots.recent(MAX_SPELLING_SNAPSHOTS),
            bound,
        };
        let surface_guard = speller.guard(guard)?;
        let surface_consequent = speller.comparison(consequent)?;
        let lowers_to = |surface: &ClickProposition, kernel: &Proposition| {
            self.lower_surface_proposition(surface, "guarded simp premise")
                .is_ok_and(|lowered| {
                    lowered == *kernel || condition_polarity_equivalent(&lowered, kernel)
                })
        };
        (lowers_to(&surface_guard, guard) && lowers_to(&surface_consequent, consequent))
            .then_some((surface_guard, surface_consequent))
    }
}

type BinaryExpression = fn(Box<ContractExpression>, Box<ContractExpression>) -> ContractExpression;

/// The operands and the written operator of a no-overflow condition.
fn overflow_operands(
    condition: &ConditionTerm,
) -> Option<(&Bitvector32Term, &Bitvector32Term, BinaryExpression)> {
    let (left, right, construct): (_, _, BinaryExpression) = match condition {
        ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
            (left, right, ContractExpression::Add)
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
            (left, right, ContractExpression::Subtract)
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
            (left, right, ContractExpression::Multiply)
        }
        _ => return None,
    };
    Some((left, right, construct))
}

/// The recorded snapshots consulted for an earlier model-field value.
const MAX_SPELLING_SNAPSHOTS: usize = 16;

/// The distinct model-field accesses written in a goal.
fn collect_goal_field_accesses(
    proposition: &ClickProposition,
    accesses: &mut Vec<ResourceFieldAccess>,
) {
    let mut pending_propositions = vec![proposition];
    let mut pending_expressions = Vec::new();
    while let Some(proposition) = pending_propositions.pop() {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                pending_expressions.push(left);
                pending_expressions.push(right);
            }
            ClickProposition::Defined { expression } => pending_expressions.push(expression),
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending_propositions.push(left);
                pending_propositions.push(right);
            }
            ClickProposition::Not(inner) => pending_propositions.push(inner),
            _ => {}
        }
    }
    while let Some(expression) = pending_expressions.pop() {
        match expression {
            ContractExpression::ResourceField(access) => {
                if !accesses.contains(access) {
                    accesses.push(access.clone());
                }
            }
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                pending_expressions.push(left);
                pending_expressions.push(right);
            }
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => pending_expressions.push(inner),
            _ => {}
        }
    }
}

struct GuardedTermSpeller<'v, 'p> {
    view: &'v FixedStateOperationView<'p>,
    accesses: &'v [ResourceFieldAccess],
    snapshots: Vec<(&'p SnapshotSelector, &'p CState)>,
    /// Binders an enclosing `intro` named, by their kernel variables.
    bound: BTreeMap<Variable, String>,
}

impl GuardedTermSpeller<'_, '_> {
    fn guard(&self, guard: &Proposition) -> Option<ClickProposition> {
        match guard {
            Proposition::And(left, right) => Some(ClickProposition::And(
                Box::new(self.guard(left)?),
                Box::new(self.guard(right)?),
            )),
            Proposition::ConditionIs(condition, false)
                if let Some((left, right, construct)) = overflow_operands(condition) =>
            {
                Some(ClickProposition::Defined {
                    expression: construct(Box::new(self.term(left)?), Box::new(self.term(right)?)),
                })
            }
            _ => self.comparison(guard),
        }
    }

    /// An int32 or int64 comparison, in either polarity.
    fn comparison(&self, proposition: &Proposition) -> Option<ClickProposition> {
        let Proposition::ConditionIs(condition, value) = proposition else {
            return None;
        };
        // The ordinary synthesis spells a comparison over current names and
        // the enclosing binders whole; the pieces below cover what it cannot
        // name (an earlier model field, a local out of scope).
        if !self.bound.is_empty()
            && let Some(whole) = synthesize_surface_proposition_with_bound_variable_names(
                proposition,
                self.view.parameters,
                self.view.arguments,
                self.view.state,
                &self.bound,
            )
        {
            return Some(whole);
        }
        let (left, right, operator) = match condition {
            ConditionTerm::Bitvector32Equal(left, right)
            | ConditionTerm::Bitvector64Equal(left, right) => {
                (left, right, ComparisonOperator::Equal)
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right)
            | ConditionTerm::Bitvector64SignedLessThan(left, right) => {
                (left, right, ComparisonOperator::LessThan)
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
            | ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
                (left, right, ComparisonOperator::LessEqual)
            }
            ConditionTerm::Bitvector32SignedGreaterThan(left, right)
            | ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
                (left, right, ComparisonOperator::GreaterThan)
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
            | ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
                (left, right, ComparisonOperator::GreaterEqual)
            }
            _ => return None,
        };
        let operator = if *value {
            operator
        } else {
            match operator {
                ComparisonOperator::Equal => ComparisonOperator::NotEqual,
                ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
                ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
                ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
                ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
                ComparisonOperator::NotEqual | ComparisonOperator::In => return None,
            }
        };
        Some(ClickProposition::Comparison {
            left: self.term(left)?,
            operator,
            right: self.term(right)?,
        })
    }

    fn field_value<'s>(
        state: &'s CState,
        access: &ResourceFieldAccess,
    ) -> Option<&'s Bitvector32Term> {
        match state
            .resource_instance_at_path(access.identity, &access.children)?
            .fields()
            .get(access.field_index)?
        {
            AlgebraicValue::C(
                CValue::Int8(value)
                | CValue::Int16(value)
                | CValue::Int32(value)
                | CValue::UInt8(value)
                | CValue::UInt16(value)
                | CValue::UInt32(value)
                | CValue::Int64(value)
                | CValue::UInt64(value),
            ) => Some(value),
            _ => None,
        }
    }

    /// A model field the goal names, read at the current state, at function
    /// entry, or at the newest recorded snapshot that holds this value.
    fn field_spelling(&self, term: &Bitvector32Term) -> Option<ContractExpression> {
        let named = |access: &ResourceFieldAccess| {
            Box::new(ContractExpression::ResourceField(access.clone()))
        };
        for access in self.accesses {
            if Self::field_value(self.view.state, access) == Some(term) {
                return Some(*named(access));
            }
        }
        for access in self.accesses {
            if Self::field_value(self.view.pre_state, access) == Some(term) {
                return Some(ContractExpression::Old(named(access)));
            }
        }
        for (selector, state) in self.preferred_snapshots() {
            for access in self.accesses {
                if Self::field_value(state, access) == Some(term) {
                    return Some(ContractExpression::At {
                        selector: (*selector).clone(),
                        expression: named(access),
                    });
                }
            }
        }
        None
    }

    fn term(&self, term: &Bitvector32Term) -> Option<ContractExpression> {
        if let Bitvector32Term::Variable(variable) = term
            && let Some(name) = self.bound.get(variable)
        {
            return Some(ContractExpression::CFragment(CExpression::Variable(
                name.clone(),
            )));
        }
        if let Some(field) = self.field_spelling(term) {
            return Some(field);
        }
        let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
            Some((Box::new(self.term(left)?), Box::new(self.term(right)?)))
        };
        let composite =
            match term {
                Bitvector32Term::Add(left, right) => {
                    binary(left, right).map(|(left, right)| ContractExpression::Add(left, right))
                }
                Bitvector32Term::Subtract(left, right) => binary(left, right)
                    .map(|(left, right)| ContractExpression::Subtract(left, right)),
                Bitvector32Term::Multiply(left, right)
                | Bitvector32Term::Int64Multiply(left, right) => binary(left, right)
                    .map(|(left, right)| ContractExpression::Multiply(left, right)),
                Bitvector32Term::Int64Add(left, right) => {
                    binary(left, right).map(|(left, right)| ContractExpression::Add(left, right))
                }
                Bitvector32Term::Int64Subtract(left, right) => binary(left, right)
                    .map(|(left, right)| ContractExpression::Subtract(left, right)),
                _ => None,
            };
        composite
            .or_else(|| {
                synthesize_surface_machine_expression(
                    term,
                    self.view.parameters,
                    self.view.arguments,
                    self.view.state,
                )
            })
            .or_else(|| {
                // A local that has left scope (a returned path's locals)
                // still reads at the recorded point that held it.
                self.preferred_snapshots().find_map(|(selector, state)| {
                    let expression = synthesize_surface_machine_expression(
                        term,
                        self.view.parameters,
                        self.view.arguments,
                        state,
                    )?;
                    Some(ContractExpression::At {
                        selector: (*selector).clone(),
                        expression: Box::new(expression),
                    })
                })
            })
    }

    /// Named marks first: they are the author's own stable spelling.
    fn preferred_snapshots(&self) -> impl Iterator<Item = &(&SnapshotSelector, &CState)> {
        self.snapshots
            .iter()
            .filter(|(selector, _)| matches!(selector, SnapshotSelector::Mark(_)))
            .chain(
                self.snapshots
                    .iter()
                    .filter(|(selector, _)| !matches!(selector, SnapshotSelector::Mark(_))),
            )
    }
}
