//! Smart closure through a definedness-guarded comparison.
//!
//! Lowering a partial C expression such as `old(st.live) + result` at a call
//! or a return keeps its no-overflow condition as the antecedent of the
//! equality it states: `defined(old(st.live) + result) implies st.live ==
//! old(st.live) + result`. The kernel does not harvest such a consequent on
//! its own; the checked `extract` rule does once the guard is an available
//! fact. This closer selects the guarded comparisons whose consequent shares
//! an operand with the goal, proves each guard with an ordinary nested
//! `solve` (the bounded overflow-interval reasoning decides it from the
//! operands' bounds), extracts the consequent, and continues the closure.
//! Expansion therefore renders the discharge as `have defined(..) by { .. }`
//! followed by `extract(..)`. An implication under an ordinary condition is
//! not selected here: its antecedent is never proved by a nested search. The
//! direct logical closure applies one only when its antecedent is already
//! exactly available (`try_discharged_consequent_closure`).

use super::*;
use crate::kernel::MachineBinaryOp;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
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
    /// Spell the guard and the consequent of one selected guarded equality
    /// so each lowers back to exactly its kernel form. Terms read from the
    /// model fields the goal names are spelled through those fields at the
    /// current state, the function entry, or a recorded state; other terms
    /// take the ordinary bounded synthesis. A candidate that does not lower
    /// back to its kernel form is not offered.
    fn guarded_implication_surfaces(
        &self,
        guard: &Proposition,
        consequent: &Proposition,
    ) -> Option<(ClickProposition, ClickProposition)> {
        let (surface_guard, surface_consequent) = self.with_guarded_term_speller(|speller| {
            Some((speller.guard(guard)?, speller.comparison(consequent)?))
        })?;
        let surface_consequent =
            super::smart_closures::observed_native_arithmetic(consequent, &surface_consequent);
        (self.surface_lowers_to(&surface_guard, guard)
            && self.surface_lowers_to(&surface_consequent, consequent))
        .then_some((surface_guard, surface_consequent))
    }

    /// Spell one order or equality comparison from the current state's
    /// names, accepted only when the spelling lowers back to `kernel`. Solve
    /// uses it for a selected bound that has no recorded spelling of its
    /// own: a leaf conjunct of a written fact, whose recorded spelling is the
    /// whole conjunction, or a branch condition's negation.
    pub(super) fn spelled_comparison_surface(
        &self,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        let surface = self.with_guarded_term_speller(|speller| speller.comparison(kernel))?;
        self.surface_lowers_to(&surface, kernel).then_some(surface)
    }

    fn surface_lowers_to(&self, surface: &ClickProposition, kernel: &Proposition) -> bool {
        self.lower_surface_proposition(surface, "guarded solve premise")
            .is_ok_and(|lowered| {
                lowered == *kernel
                    || condition_polarity_equivalent(&lowered, kernel)
                    || super::smart_closures::propositions_match_after_canonical_loads(
                        &lowered, kernel,
                    )
            })
    }

    fn with_guarded_term_speller<R>(
        &self,
        spell: impl FnOnce(&GuardedTermSpeller) -> Option<R>,
    ) -> Option<R> {
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
                        ContractExpression::ProgramExpression(ProgramExpression::Value(
                            crate::kernel::integer64_c_value!(MachineTerm::Variable(variable)),
                        )) => Some((*variable, name.clone())),
                        _ => None,
                    })
                    .collect::<BTreeMap<_, _>>()
            })
            .unwrap_or_default();
        spell(&GuardedTermSpeller {
            view: &view,
            accesses: &accesses,
            retained_states: view.fixed_state.recorded_states.recent(MAX_SPELLING_STATES),
            bound,
        })
    }
}

type BinaryExpression = fn(Box<ContractExpression>, Box<ContractExpression>) -> ContractExpression;

/// The operands and the written operator of a no-overflow condition.
fn overflow_operands(
    condition: &ConditionTerm,
) -> Option<(&MachineTerm, &MachineTerm, BinaryExpression)> {
    let (left, right, construct): (_, _, BinaryExpression) = match condition {
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left,
            right,
        }
        | ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Add,
            left,
            right,
        } => (left, right, ContractExpression::Add),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Subtract,
            left,
            right,
        }
        | ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Subtract,
            left,
            right,
        } => (left, right, ContractExpression::Subtract),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Multiply,
            left,
            right,
        }
        | ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Multiply,
            left,
            right,
        } => (left, right, ContractExpression::Multiply),
        _ => return None,
    };
    Some((left, right, construct))
}

/// The recorded states consulted for an earlier model-field value.
const MAX_SPELLING_STATES: usize = 16;

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
            // An exact observation names the field it observes.
            ContractExpression::Call { name, arguments } if name == "to_integer" => {
                pending_expressions.extend(arguments);
            }
            _ => {}
        }
    }
}

struct GuardedTermSpeller<'v, 'p> {
    view: &'v FixedStateOperationView<'p>,
    accesses: &'v [ResourceFieldAccess],
    retained_states: Vec<(&'p ProgramPointSelector, &'p ExecutionState)>,
    /// Binders an enclosing `intro` named, by their kernel variables.
    bound: BTreeMap<Variable, String>,
}

impl GuardedTermSpeller<'_, '_> {
    fn guard(&self, guard: &Proposition) -> Option<ClickProposition> {
        // Complete ordinary range guards name the same operation as the
        // former private overflow query. Keep model-field state names on
        // its operands; the caller checks the full domain's round trip.
        let query = crate::kernel::machine_integer::definedness::interval_query_form(guard);
        let guard = query.as_ref().unwrap_or(guard);
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
                self.view.parameter_binding,
                self.view.fixed_state.state,
                &self.bound,
            )
        {
            return Some(whole);
        }
        let view =
            crate::kernel::machine_integer::comparison::structural_comparison_view(condition)?;
        if !matches!(
            view.format,
            MachineIntegerType::Int32 | MachineIntegerType::Int64
        ) && !(matches!(
            view.format,
            MachineIntegerType::UInt32 | MachineIntegerType::UInt64
        ) && view.relation == CompareRelation::Equal)
        {
            return None;
        }
        let operator = match view.relation {
            CompareRelation::Equal => ComparisonOperator::Equal,
            CompareRelation::LessThan => ComparisonOperator::LessThan,
            CompareRelation::LessEqual => ComparisonOperator::LessEqual,
            CompareRelation::GreaterThan => ComparisonOperator::GreaterThan,
            CompareRelation::GreaterEqual => ComparisonOperator::GreaterEqual,
        };
        let operator = if *value != view.negated {
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
            left: self.operand(view.operands[0].operand_view())?,
            operator,
            right: self.operand(view.operands[1].operand_view())?,
        })
    }

    fn operand(&self, value: crate::kernel::MachineOperandView<'_>) -> Option<ContractExpression> {
        use crate::kernel::MachineOperandView as V;
        let V::Shared(root) = value else {
            let V::Legacy(value) = value else {
                unreachable!()
            };
            return self.term(value);
        };
        if let Some(value) = root
            .machine_conversion_leaf()
            .or_else(|| root.machine_read_leaf())
        {
            return self.term(value);
        }
        if let Some(value) = value
            .literal()
            .or_else(|| value.variable().copied().map(MachineTerm::Variable))
        {
            return self.term(&value);
        }
        if let Some((MachineIntegerType::Int32 | MachineIntegerType::Int64, op, [a, b])) =
            value.binary()
        {
            let construct: BinaryExpression = match op {
                MachineBinaryOp::Add => ContractExpression::Add,
                MachineBinaryOp::Subtract => ContractExpression::Subtract,
                MachineBinaryOp::Multiply => ContractExpression::Multiply,
                _ => {
                    return super::surface_synthesis::raise_kernel_term(
                        root,
                        self.view.parameter_binding,
                        self.view.fixed_state.state,
                        &self.bound,
                    );
                }
            };
            return Some(construct(
                Box::new(self.operand(a)?),
                Box::new(self.operand(b)?),
            ));
        }
        super::surface_synthesis::raise_kernel_term(
            root,
            self.view.parameter_binding,
            self.view.fixed_state.state,
            &self.bound,
        )
    }

    fn field_value<'s>(
        state: &'s ExecutionState,
        access: &ResourceFieldAccess,
    ) -> Option<&'s MachineTerm> {
        match state
            .resource_instance_at_path(access.identity, &access.children)?
            .fields()
            .get(access.field_index)?
        {
            AlgebraicValue::Program(crate::kernel::integer64_c_value!(value)) => Some(value),
            _ => None,
        }
    }

    /// A model field the goal names, read at the current state, at function
    /// entry, or at the newest recorded state that holds this value.
    fn field_spelling(&self, term: &MachineTerm) -> Option<ContractExpression> {
        let named = |access: &ResourceFieldAccess| {
            Box::new(ContractExpression::ResourceField(access.clone()))
        };
        for access in self.accesses {
            if Self::field_value(self.view.fixed_state.state, access) == Some(term) {
                return Some(*named(access));
            }
        }
        for access in self.accesses {
            if Self::field_value(self.view.fixed_state.pre_state, access) == Some(term) {
                return Some(ContractExpression::Old(named(access)));
            }
        }
        for (selector, state) in self.preferred_states() {
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

    fn term(&self, term: &MachineTerm) -> Option<ContractExpression> {
        if let MachineTerm::Variable(variable) = term
            && let Some(name) = self.bound.get(variable)
        {
            return Some(ContractExpression::ProgramExpression(
                ProgramExpression::Variable(name.clone()),
            ));
        }
        if let Some(field) = self.field_spelling(term) {
            return Some(field);
        }
        let binary = |left: &MachineTerm, right: &MachineTerm| {
            Some((Box::new(self.term(left)?), Box::new(self.term(right)?)))
        };
        let composite = match term {
            binary_term!(Int32, Add, left, right) => {
                binary(left, right).map(|(left, right)| ContractExpression::Add(left, right))
            }
            binary_term!(Int32, Subtract, left, right) => {
                binary(left, right).map(|(left, right)| ContractExpression::Subtract(left, right))
            }
            binary_term!(Int32, Multiply, left, right)
            | MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Multiply,
                left,
                right,
            } => binary(left, right).map(|(left, right)| ContractExpression::Multiply(left, right)),
            MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Add,
                left,
                right,
            } => binary(left, right).map(|(left, right)| ContractExpression::Add(left, right)),
            MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Subtract,
                left,
                right,
            } => binary(left, right).map(|(left, right)| ContractExpression::Subtract(left, right)),
            _ => None,
        };
        composite
            .or_else(|| {
                synthesize_surface_machine_expression(
                    term,
                    self.view.parameter_binding,
                    self.view.fixed_state.state,
                )
            })
            .or_else(|| {
                // A local that has left scope (a returned path's locals)
                // still reads at the recorded point that held it.
                self.preferred_states().find_map(|(selector, state)| {
                    let expression = synthesize_surface_machine_expression(
                        term,
                        self.view.parameter_binding,
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
    fn preferred_states(&self) -> impl Iterator<Item = &(&ProgramPointSelector, &ExecutionState)> {
        self.retained_states
            .iter()
            .filter(|(selector, _)| matches!(selector, ProgramPointSelector::Mark(_)))
            .chain(
                self.retained_states
                    .iter()
                    .filter(|(selector, _)| !matches!(selector, ProgramPointSelector::Mark(_))),
            )
    }
}

mod search;
