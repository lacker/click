//! Smart closure through a definedness-guarded equality.
//!
//! Lowering a partial C expression such as `old(st.live) + result` at a call
//! or a return keeps its no-overflow condition as the antecedent of the
//! equality it states: `defined(old(st.live) + result) implies st.live ==
//! old(st.live) + result`. The kernel does not harvest such a consequent on
//! its own; the checked `extract` rule does once the guard is an available
//! fact. This closer selects the guarded equalities whose consequent shares an
//! operand with the goal, proves each guard with an ordinary nested `simp`
//! (the bounded overflow-interval reasoning decides it from the operands'
//! bounds), extracts the consequent, and continues the closure. Expansion
//! therefore renders the discharge as `have defined(..) by { .. }` followed
//! by `extract(..)`.

use super::*;
use std::cell::Cell;

/// At most this many guarded equalities are tried for one goal.
const MAX_GUARDED_CANDIDATES: usize = 4;

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
        let candidates = self.facts().guarded_equalities_mentioning(goal);
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
            if self.facts().contains(consequent) {
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
            // The consequent names a goal operand: rewriting the goal with it
            // leaves the operands' own facts to close what remains.
            if let Some(rewritten) = attempt::candidate_outcome(
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
        let speller = GuardedTermSpeller {
            view: &view,
            accesses: &accesses,
            snapshots: view.recorded_snapshots.recent(MAX_SPELLING_SNAPSHOTS),
        };
        let surface_guard = speller.guard(guard)?;
        let surface_consequent = speller.equality(consequent)?;
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
}

impl GuardedTermSpeller<'_, '_> {
    fn guard(&self, guard: &Proposition) -> Option<ClickProposition> {
        match guard {
            Proposition::And(left, right) => Some(ClickProposition::And(
                Box::new(self.guard(left)?),
                Box::new(self.guard(right)?),
            )),
            Proposition::ConditionIs(condition, false) => {
                let (left, right, construct): (
                    _,
                    _,
                    fn(Box<ContractExpression>, Box<ContractExpression>) -> ContractExpression,
                ) = match condition {
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
                Some(ClickProposition::Defined {
                    expression: construct(Box::new(self.term(left)?), Box::new(self.term(right)?)),
                })
            }
            _ => None,
        }
    }

    fn equality(&self, consequent: &Proposition) -> Option<ClickProposition> {
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(left, right)
            | ConditionTerm::Bitvector64Equal(left, right),
            true,
        ) = consequent
        else {
            return None;
        };
        Some(ClickProposition::Comparison {
            left: self.term(left)?,
            operator: ComparisonOperator::Equal,
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
