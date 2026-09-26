//! Smart closure of an `int64` definedness goal from the operands' bounds.
//!
//! `defined(a + b)` and `defined(a - b)` over `int64` lower to the negated
//! signed-overflow condition. The checked `int64_defined` rule of the special
//! arithmetic certificate family establishes it from each operand's width
//! range and cited constant bounds. This closer only selects those bounds:
//! the constant order and equality facts indexed under each operand term,
//! or, for `simp() using`, the listed premises that bound an operand. It
//! spells each cited fact through the goal's own operand spelling, so the
//! certificate re-lowers to exactly the facts it names. Selection is a keyed
//! lookup per operand and never scans the context; the kernel checker, not
//! this selector, decides whether the ranges exclude overflow.

use super::*;
use crate::kernel::proof::arithmetic_special::{
    int64_constant_bound_on, int64_definedness_operands,
};

impl<'a> Proof<'a> {
    /// `simp` on an `int64` definedness goal: cite the constant bounds the
    /// context indexes under each operand.
    pub(super) fn try_int64_definedness_closure(&self) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some((left, right, _)) = int64_definedness_operands(goal) else {
            return Ok(None);
        };
        let Some((surface_left, surface_right)) = self.int64_definedness_surface_operands() else {
            return Ok(None);
        };
        let assumptions = self.facts().assumptions();
        let mut premises = Vec::new();
        let mut operands = vec![(left, surface_left)];
        if right != left {
            operands.push((right, surface_right));
        }
        for (term, surface) in operands {
            for fact in assumptions.int64_constant_bound_facts(term) {
                let Some(spelled) = spell_int64_bound(&fact, term, surface) else {
                    continue;
                };
                if !premises.contains(&spelled) {
                    premises.push(spelled);
                }
            }
        }
        self.apply_int64_definedness_certificate(premises)
    }

    /// `simp() using { .. }` on an `int64` definedness goal: cite exactly the
    /// listed premises that bound an operand by a constant.
    pub(super) fn try_restricted_int64_definedness_closure(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some((left, right, _)) = int64_definedness_operands(goal) else {
            return Ok(None);
        };
        let premises = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                int64_constant_bound_on(kernel, left).is_some()
                    || int64_constant_bound_on(kernel, right).is_some()
            })
            .map(|(_, surface)| surface.clone())
            .collect::<Vec<_>>();
        self.apply_int64_definedness_certificate(premises)
    }

    fn int64_definedness_surface_operands(
        &self,
    ) -> Option<(&ContractExpression, &ContractExpression)> {
        let ClickProposition::Defined { expression } = self.surface_goal()? else {
            return None;
        };
        match expression {
            ContractExpression::Add(left, right) | ContractExpression::Subtract(left, right) => {
                Some((left.as_ref(), right.as_ref()))
            }
            _ => None,
        }
    }

    fn apply_int64_definedness_certificate(
        &self,
        premises: Vec<ClickProposition>,
    ) -> Result<Option<Self>, ClickError> {
        let Some(surface_goal) = self.surface_goal() else {
            return Ok(None);
        };
        let certificate = ArithmeticCertificate::special(SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::Int64Defined {
                bounds: (0..premises.len()).collect(),
                result: surface_goal.clone(),
            }],
            premises,
            conclusion: 0,
        });
        let Some(proof) = attempt::candidate_outcome(
            self.apply_step(ProofStep::ArithmeticCertificate(certificate)),
        )?
        else {
            return Ok(None);
        };
        Ok(proof.focused_discharged().then_some(proof))
    }
}

/// Spell one constant `int64` bound fact on `term` with `term`'s spelling
/// from the goal, in the fact's own orientation and polarity.
fn spell_int64_bound(
    fact: &Proposition,
    term: &Bitvector32Term,
    surface: &ContractExpression,
) -> Option<ClickProposition> {
    let Proposition::ConditionIs(condition, value) = fact else {
        return None;
    };
    let (left, right, operator) = match condition {
        ConditionTerm::Bitvector64Equal(left, right) => (left, right, ComparisonOperator::Equal),
        ConditionTerm::Bitvector64SignedLessThan(left, right) => {
            (left, right, ComparisonOperator::LessThan)
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
            (left, right, ComparisonOperator::LessEqual)
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
            (left, right, ComparisonOperator::GreaterThan)
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
            (left, right, ComparisonOperator::GreaterEqual)
        }
        _ => return None,
    };
    let side = |side: &Bitvector32Term| {
        if side == term {
            Some(surface.clone())
        } else {
            side.int64_as_const().map(int64_literal)
        }
    };
    let comparison = ClickProposition::Comparison {
        left: side(left)?,
        operator,
        right: side(right)?,
    };
    Some(if *value {
        comparison
    } else {
        ClickProposition::Not(Box::new(comparison))
    })
}

fn int64_literal(value: i64) -> ContractExpression {
    let magnitude = ContractExpression::IntegerLiteral(value.unsigned_abs().to_string());
    if value < 0 {
        ContractExpression::Negate(Box::new(magnitude))
    } else {
        magnitude
    }
}
