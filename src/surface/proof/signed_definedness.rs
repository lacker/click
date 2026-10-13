//! Smart closure of an `int32` or `int64` definedness goal from the
//! operands' bounds.
//!
//! `defined(a + b)` and `defined(a - b)` over `int32` or `int64` lower to the
//! negated signed-overflow condition of that width. The checked
//! `int32_defined` / `int64_defined` rule of the `rules` arithmetic
//! certificate family establishes it from each operand's width range and
//! cited constant bounds. This closer only selects those bounds: the constant
//! order and equality facts of the goal's width indexed under each operand
//! term, or, for `simp() using`, the listed premises that bound an operand.
//! It spells each cited fact through the goal's own operand spelling, so the
//! certificate re-lowers to exactly the facts it names. Selection is a keyed
//! lookup per operand and never scans the context; the kernel checker, not
//! this selector, decides whether the ranges exclude overflow. Both widths
//! share every line of this selection; the width only chooses which index
//! and comparison family the lookups read.

use super::surface_synthesis::synthesize_surface_machine_expression;
use super::*;
use crate::kernel::SignedDefinedWidth;
use crate::kernel::proof::arithmetic_special::{
    signed_constant_bound_on, signed_definedness_operands, signed_width_constant,
};

impl<'a> Proof<'a> {
    /// `simp` on an `int32` or `int64` definedness goal: cite the constant
    /// bounds the context indexes under each operand.
    pub(in crate::surface::proof) fn try_signed_definedness_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some((surface_left, surface_right)) = self.signed_definedness_surface_operands() else {
            return Ok(None);
        };
        let Some((width, left, right, _)) = signed_definedness_operands(goal) else {
            // `defined(a + b)` over operands that carry definedness of their
            // own lowers to a conjunction; its outermost operation is the
            // overflow conjunct no other conjunct takes as an operand.
            for (width, left, right) in outermost_overflow_conjuncts(goal) {
                let operands = [(left, surface_left), (right, surface_right)];
                if let Some(closed) =
                    self.try_signed_definedness_with_operand_definedness(width, operands)?
                {
                    return Ok(Some(closed));
                }
                if let Some(closed) =
                    self.try_signed_definedness_after_operand_substitution(width, operands)?
                {
                    return Ok(Some(closed));
                }
            }
            return Ok(None);
        };
        let premises = self
            .signed_operand_bound_premises(width, [(left, surface_left), (right, surface_right)]);
        if let Some(closed) = self.apply_signed_definedness_certificate(width, premises)? {
            return Ok(Some(closed));
        }
        self.try_signed_definedness_after_operand_substitution(
            width,
            [(left, surface_left), (right, surface_right)],
        )
    }

    /// The constant bounds the context indexes under each operand, spelled
    /// through the operand's spelling in the goal.
    fn signed_operand_bound_premises(
        &self,
        width: SignedDefinedWidth,
        operands: [(&Bitvector32Term, &ContractExpression); 2],
    ) -> Vec<ClickProposition> {
        let assumptions = self.facts().assumptions();
        let mut premises = Vec::new();
        for (term, surface) in operands {
            for fact in assumptions.signed_constant_bound_facts(width, term) {
                let Some(spelled) = spell_signed_bound(width, &fact, term, surface) else {
                    continue;
                };
                if !premises.contains(&spelled) {
                    premises.push(spelled);
                }
            }
        }
        premises
    }

    /// A definedness goal that lowers to a conjunction with its operands'
    /// own definedness, such as `defined(pool->capacity - 1)` over a read
    /// through a resource view: each written operand's `defined(..)` is
    /// proved as a `have` by `simp` and cited beside the operands' bounds,
    /// which the `int32_defined` / `int64_defined` rule accepts for the
    /// conjuncts beyond the operation's overflow.
    fn try_signed_definedness_with_operand_definedness(
        &self,
        width: SignedDefinedWidth,
        operands: [(&Bitvector32Term, &ContractExpression); 2],
    ) -> Result<Option<Self>, ClickError> {
        let mut premises = self.signed_operand_bound_premises(width, operands);
        if premises.is_empty() {
            return Ok(None);
        }
        let mut proof = self.clone();
        for (term, surface) in operands {
            if signed_width_constant(width, term).is_some() {
                continue;
            }
            let defined = ClickProposition::Defined {
                expression: surface.clone(),
            };
            if premises.contains(&defined) {
                continue;
            }
            let Ok(scope) = proof.begin_have(defined.clone()) else {
                return Ok(None);
            };
            let Some(scope) = scope.try_simp_closure()? else {
                return Ok(None);
            };
            proof = scope.join()?;
            premises.push(defined);
        }
        proof.apply_signed_definedness_certificate(width, premises)
    }

    /// An operand whose summands are fixed by exact constant equalities,
    /// such as a count `A + n` with `A == 0`, is first restated without
    /// them: `count == n` is proved as a `have` by `simp`, `defined(n + 1)`
    /// as a `have` from the bounds of `n`, and the goal, rewritten by the
    /// first, closes from both. Each summand is a keyed lookup; nothing
    /// scans the context.
    fn try_signed_definedness_after_operand_substitution(
        &self,
        width: SignedDefinedWidth,
        operands: [(&Bitvector32Term, &ContractExpression); 2],
    ) -> Result<Option<Self>, ClickError> {
        let Some(ClickProposition::Defined { expression }) = self.surface_goal() else {
            return Ok(None);
        };
        let assumptions = self.facts().assumptions();
        let mut proof = self.clone();
        let mut equalities = Vec::new();
        let mut restated = Vec::new();
        for (term, surface) in operands {
            let simpler = substitute_constant_summands(width, term, &|summand| {
                assumptions
                    .signed_constant_bound_facts(width, summand)
                    .iter()
                    .find_map(|fact| exact_constant_of(width, fact, summand))
            })
            .and_then(|substituted| self.synthesize_machine_term_here(&substituted));
            let Some(simpler) = simpler else {
                restated.push(surface.clone());
                continue;
            };
            let equality = ClickProposition::Comparison {
                left: surface.clone(),
                operator: ComparisonOperator::Equal,
                right: simpler.clone(),
            };
            if equalities.contains(&equality) {
                restated.push(simpler);
                continue;
            }
            let Ok(scope) = proof.begin_have(equality.clone()) else {
                return Ok(None);
            };
            let Some(scope) = scope.try_simp_closure()? else {
                return Ok(None);
            };
            proof = scope.join()?;
            equalities.push(equality);
            restated.push(simpler);
        }
        if equalities.is_empty() {
            return Ok(None);
        }
        let [left, right]: [ContractExpression; 2] = restated
            .try_into()
            .expect("one restated spelling per operand");
        let defined = ClickProposition::Defined {
            expression: match expression {
                ContractExpression::Subtract(_, _) => {
                    ContractExpression::Subtract(Box::new(left), Box::new(right))
                }
                _ => ContractExpression::Add(Box::new(left), Box::new(right)),
            },
        };
        let Ok(scope) = proof.begin_have(defined) else {
            return Ok(None);
        };
        let Some(scope) = scope.try_signed_definedness_closure()? else {
            return Ok(None);
        };
        let mut proof = scope.join()?;
        for equality in equalities {
            let Ok(rewritten) = proof.apply_step(ProofStep::Rewrite(equality)) else {
                return Ok(None);
            };
            proof = rewritten;
        }
        if proof.is_complete() {
            return Ok(Some(proof));
        }
        proof.try_direct_logical_closure()
    }

    fn synthesize_machine_term_here(&self, term: &Bitvector32Term) -> Option<ContractExpression> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => synthesize_surface_machine_expression(
                term,
                context.parameter_binding,
                context.fixed_state.state,
            ),
            ProofContext::Execution(_) => {
                let view = self.premise_fixed_state_view()?;
                synthesize_surface_machine_expression(
                    term,
                    view.parameter_binding,
                    view.fixed_state.state,
                )
            }
        }
    }

    /// `simp() using { .. }` on an `int32` or `int64` definedness goal: cite
    /// exactly the listed premises that bound an operand by a constant.
    pub(super) fn try_restricted_signed_definedness_closure(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some((width, left, right, _)) = signed_definedness_operands(goal) else {
            return Ok(None);
        };
        let premises = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                signed_constant_bound_on(width, kernel, left).is_some()
                    || signed_constant_bound_on(width, kernel, right).is_some()
            })
            .map(|(_, surface)| surface.clone())
            .collect::<Vec<_>>();
        self.apply_signed_definedness_certificate(width, premises)
    }

    fn signed_definedness_surface_operands(
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

    fn apply_signed_definedness_certificate(
        &self,
        width: SignedDefinedWidth,
        premises: Vec<ClickProposition>,
    ) -> Result<Option<Self>, ClickError> {
        let Some(surface_goal) = self.surface_goal() else {
            return Ok(None);
        };
        let certificate = ArithmeticCertificate::special(SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::SignedDefined {
                width,
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

/// Spell one constant bound fact of `width` on `term` with `term`'s spelling
/// from the goal, in the fact's own orientation and polarity.
fn spell_signed_bound(
    width: SignedDefinedWidth,
    fact: &Proposition,
    term: &Bitvector32Term,
    surface: &ContractExpression,
) -> Option<ClickProposition> {
    let Proposition::ConditionIs(condition, value) = fact else {
        return None;
    };
    let (left, right, operator) = match (width, condition) {
        (SignedDefinedWidth::Int32, ConditionTerm::Bitvector32Equal(left, right))
        | (SignedDefinedWidth::Int64, ConditionTerm::Bitvector64Equal(left, right)) => {
            (left, right, ComparisonOperator::Equal)
        }
        (SignedDefinedWidth::Int32, ConditionTerm::Bitvector32SignedLessThan(left, right))
        | (SignedDefinedWidth::Int64, ConditionTerm::Bitvector64SignedLessThan(left, right)) => {
            (left, right, ComparisonOperator::LessThan)
        }
        (SignedDefinedWidth::Int32, ConditionTerm::Bitvector32SignedLessEqual(left, right))
        | (SignedDefinedWidth::Int64, ConditionTerm::Bitvector64SignedLessEqual(left, right)) => {
            (left, right, ComparisonOperator::LessEqual)
        }
        (SignedDefinedWidth::Int32, ConditionTerm::Bitvector32SignedGreaterThan(left, right))
        | (SignedDefinedWidth::Int64, ConditionTerm::Bitvector64SignedGreaterThan(left, right)) => {
            (left, right, ComparisonOperator::GreaterThan)
        }
        (SignedDefinedWidth::Int32, ConditionTerm::Bitvector32SignedGreaterEqual(left, right))
        | (SignedDefinedWidth::Int64, ConditionTerm::Bitvector64SignedGreaterEqual(left, right)) => {
            (left, right, ComparisonOperator::GreaterEqual)
        }
        _ => return None,
    };
    let side = |side: &Bitvector32Term| {
        if side == term {
            Some(surface.clone())
        } else {
            signed_width_constant(width, side).map(signed_literal)
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

fn signed_literal(value: i64) -> ContractExpression {
    let magnitude = ContractExpression::IntegerLiteral(value.unsigned_abs().to_string());
    if value < 0 {
        ContractExpression::Negate(Box::new(magnitude))
    } else {
        magnitude
    }
}

/// The constant an exact equality fact of `width` fixes `term` to.
fn exact_constant_of(
    width: SignedDefinedWidth,
    fact: &Proposition,
    term: &Bitvector32Term,
) -> Option<i64> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(left, right) | ConditionTerm::Bitvector64Equal(left, right),
        true,
    ) = fact
    else {
        return None;
    };
    if left.as_ref() == term {
        signed_width_constant(width, right)
    } else if right.as_ref() == term {
        signed_width_constant(width, left)
    } else {
        None
    }
}

/// `term` with each summand of its sums and differences that `constant`
/// fixes to zero removed, or `None` when no summand is removed.
fn substitute_constant_summands(
    width: SignedDefinedWidth,
    term: &Bitvector32Term,
    constant: &dyn Fn(&Bitvector32Term) -> Option<i64>,
) -> Option<Bitvector32Term> {
    let zero = |summand: &Bitvector32Term| {
        signed_width_constant(width, summand).is_none() && constant(summand) == Some(0)
    };
    match term {
        Bitvector32Term::Add(left, right) => {
            if zero(left) {
                return Some(
                    substitute_constant_summands(width, right, constant)
                        .unwrap_or_else(|| right.as_ref().clone()),
                );
            }
            if zero(right) {
                return Some(
                    substitute_constant_summands(width, left, constant)
                        .unwrap_or_else(|| left.as_ref().clone()),
                );
            }
            let new_left = substitute_constant_summands(width, left, constant);
            let new_right = substitute_constant_summands(width, right, constant);
            (new_left.is_some() || new_right.is_some()).then(|| {
                Bitvector32Term::Add(
                    Box::new(new_left.unwrap_or_else(|| left.as_ref().clone())),
                    Box::new(new_right.unwrap_or_else(|| right.as_ref().clone())),
                )
            })
        }
        Bitvector32Term::Subtract(left, right) => {
            if zero(right) {
                return Some(
                    substitute_constant_summands(width, left, constant)
                        .unwrap_or_else(|| left.as_ref().clone()),
                );
            }
            let new_left = substitute_constant_summands(width, left, constant)?;
            Some(Bitvector32Term::Subtract(Box::new(new_left), right.clone()))
        }
        _ => None,
    }
}

/// The overflow conjuncts of a definedness conjunction whose operation is
/// not itself an operand of another conjunct: the candidates for the
/// written expression's outermost operation.
fn outermost_overflow_conjuncts(
    goal: &Proposition,
) -> Vec<(SignedDefinedWidth, &Bitvector32Term, &Bitvector32Term)> {
    fn collect<'a>(
        proposition: &'a Proposition,
        out: &mut Vec<(
            SignedDefinedWidth,
            &'a Bitvector32Term,
            &'a Bitvector32Term,
            bool,
        )>,
    ) {
        match proposition {
            Proposition::And(left, right) => {
                collect(left, out);
                collect(right, out);
            }
            other => out.extend(signed_definedness_operands(other)),
        }
    }
    let Proposition::And(_, _) = goal else {
        return Vec::new();
    };
    let mut conjuncts = Vec::new();
    collect(goal, &mut conjuncts);
    let operation = |left: &Bitvector32Term, right: &Bitvector32Term, subtract: bool| {
        let (left, right) = (Box::new(left.clone()), Box::new(right.clone()));
        if subtract {
            Bitvector32Term::Subtract(left, right)
        } else {
            Bitvector32Term::Add(left, right)
        }
    };
    conjuncts
        .iter()
        .filter(|(_, left, right, subtract)| {
            let term = operation(left, right, *subtract);
            !conjuncts.iter().any(|(_, other_left, other_right, _)| {
                **other_left == term || **other_right == term
            })
        })
        .map(|(width, left, right, _)| (*width, *left, *right))
        .collect()
}
