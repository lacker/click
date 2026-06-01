//! Shared proof-script and evaluation-proof helpers for prelude modules.

use crate::{
    Computation, Name, Outcome, Proof, Step, Theorem, Theory, alpha_eq_computation,
    computes_to_outcome,
};

use super::source::{ParsedModule, ParsedTheorem, ProofExpr, ProofScript};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvaluationProofError {
    StepLimitExceeded {
        limit: usize,
    },
    UnexpectedNormalForm {
        expected: Computation,
        actual: Computation,
    },
}

pub(super) fn proof_for_theorem(theorem: &ParsedTheorem, theory: &Theory) -> Option<Proof> {
    match &theorem.proof {
        ProofScript::Proof(proof) => proof_expr_to_proof(proof, theory),
    }
}

pub(super) fn source_theorem(
    module: ParsedModule,
    name: Name,
    mut theory: Theory,
) -> Option<Theorem> {
    for theorem in module.theorems {
        let requested = theorem.name == name;
        let proof = proof_for_theorem(&theorem, &theory)?;
        let theorem = theory.define_theorem_from_proof(theorem.name, proof, theorem.prop)?;

        if requested {
            return Some(theorem);
        }
    }

    None
}

fn proof_expr_to_proof(proof: &ProofExpr, theory: &Theory) -> Option<Proof> {
    match proof {
        ProofExpr::Known(name) => Some(Proof::Known(*name)),
        ProofExpr::Assume(symbol) => Some(Proof::Assume(*symbol)),
        ProofExpr::Symm(proof) => Some(Proof::Symm(Box::new(proof_expr_to_proof(proof, theory)?))),
        ProofExpr::Trans(first, second) => Some(Proof::Trans(
            Box::new(proof_expr_to_proof(first, theory)?),
            Box::new(proof_expr_to_proof(second, theory)?),
        )),
        ProofExpr::EvalTo {
            computation,
            expected,
            limit,
        } => proof_by_reduction_to_computation_in_theory(
            computation.clone(),
            expected.clone(),
            theory,
            *limit,
        )
        .ok(),
        ProofExpr::EvalSame { left, right, limit } => {
            proof_by_same_normal_form_in_theory(left.clone(), right.clone(), theory, *limit).ok()
        }
        ProofExpr::Rewrite {
            equality,
            proof,
            variable,
            template,
        } => Some(Proof::Rewrite {
            equality: Box::new(proof_expr_to_proof(equality, theory)?),
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
            variable: *variable,
            template: template.clone(),
        }),
        ProofExpr::ListNil => Some(Proof::ListNil),
        ProofExpr::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => Some(Proof::ImpliesIntro {
            assumption: *assumption,
            premise: premise.clone(),
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
        }),
        ProofExpr::ImpliesElim {
            implication,
            premise,
        } => Some(Proof::ImpliesElim {
            implication: Box::new(proof_expr_to_proof(implication, theory)?),
            premise: Box::new(proof_expr_to_proof(premise, theory)?),
        }),
        ProofExpr::ExistsIntro {
            variable,
            body,
            witness,
            proof,
        } => Some(Proof::ExistsIntro {
            variable: *variable,
            body: body.clone(),
            witness: witness.clone(),
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
        }),
        ProofExpr::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        } => Some(Proof::ExistsElim {
            existential: Box::new(proof_expr_to_proof(existential, theory)?),
            witness: *witness,
            assumption: *assumption,
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
        }),
        ProofExpr::AndIntro(left, right) => Some(Proof::AndIntro(
            Box::new(proof_expr_to_proof(left, theory)?),
            Box::new(proof_expr_to_proof(right, theory)?),
        )),
        ProofExpr::AndElimLeft(proof) => Some(Proof::AndElimLeft(Box::new(proof_expr_to_proof(
            proof, theory,
        )?))),
        ProofExpr::AndElimRight(proof) => Some(Proof::AndElimRight(Box::new(proof_expr_to_proof(
            proof, theory,
        )?))),
        ProofExpr::ConsIsList {
            head,
            tail,
            head_is_value,
            tail_is_list,
        } => Some(Proof::ConsIsList {
            head: head.clone(),
            tail: tail.clone(),
            head_is_value: Box::new(proof_expr_to_proof(head_is_value, theory)?),
            tail_is_list: Box::new(proof_expr_to_proof(tail_is_list, theory)?),
        }),
        ProofExpr::ListInduction {
            variable,
            property,
            base,
            head,
            tail,
            head_is_value_assumption,
            tail_is_list_assumption,
            induction_hypothesis_assumption,
            step,
        } => Some(Proof::ListInduction {
            variable: *variable,
            property: property.clone(),
            base: Box::new(proof_expr_to_proof(base, theory)?),
            head: *head,
            tail: *tail,
            head_is_value_assumption: *head_is_value_assumption,
            tail_is_list_assumption: *tail_is_list_assumption,
            induction_hypothesis_assumption: *induction_hypothesis_assumption,
            step: Box::new(proof_expr_to_proof(step, theory)?),
        }),
        ProofExpr::ForAllIntro { variable, proof } => Some(Proof::ForAllIntro {
            variable: *variable,
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
        }),
        ProofExpr::ForAllElim { forall, argument } => Some(Proof::ForAllElim {
            forall: Box::new(proof_expr_to_proof(forall, theory)?),
            argument: argument.clone(),
        }),
    }
}

pub(super) fn evaluation_chain_in_theory(
    computation: Computation,
    theory: &Theory,
    limit: usize,
) -> Result<Vec<Computation>, EvaluationProofError> {
    let mut computation = computation;
    let mut chain = vec![computation.clone()];

    for _ in 0..limit {
        match theory.reduce(&computation) {
            Step::Reduced(next) => {
                chain.push(next.clone());
                computation = next;
            }
            Step::Normal => return Ok(chain),
        }
    }

    Err(EvaluationProofError::StepLimitExceeded { limit })
}

pub(super) fn proof_by_evaluation_in_theory(
    computation: Computation,
    expected: impl Into<Outcome>,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    proof_by_evaluation_to_computation_in_theory(computation, expected.into().into(), theory, limit)
}

pub(super) fn proof_by_evaluation_to_computation_in_theory(
    computation: Computation,
    expected: Computation,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let chain = evaluation_chain_in_theory(computation, theory, limit)?;
    let actual = chain
        .last()
        .cloned()
        .expect("evaluation chains are nonempty");

    if !alpha_eq_computation(&actual, &expected) {
        return Err(EvaluationProofError::UnexpectedNormalForm { expected, actual });
    }

    Ok(Proof::Steps(chain))
}

pub(super) fn proof_by_reduction_in_theory(
    computation: Computation,
    expected: impl Into<Outcome>,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    proof_by_reduction_to_computation_in_theory(computation, expected.into().into(), theory, limit)
}

pub(super) fn proof_by_reduction_to_computation_in_theory(
    computation: Computation,
    expected: Computation,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let mut computation = computation;
    let mut chain = vec![computation.clone()];

    if alpha_eq_computation(&computation, &expected) {
        return Ok(Proof::Steps(chain));
    }

    for _ in 0..limit {
        match theory.reduce(&computation) {
            Step::Reduced(next) => {
                chain.push(next.clone());
                if alpha_eq_computation(&next, &expected) {
                    return Ok(Proof::Steps(chain));
                }
                computation = next;
            }
            Step::Normal => {
                return Err(EvaluationProofError::UnexpectedNormalForm {
                    expected,
                    actual: computation,
                });
            }
        }
    }

    Err(EvaluationProofError::StepLimitExceeded { limit })
}

pub(super) fn proof_by_same_normal_form_in_theory(
    left: Computation,
    right: Computation,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let left_normal = theory.normal_form(&left);
    let right_normal = theory.normal_form(&right);

    if !alpha_eq_computation(&left_normal, &right_normal) {
        return Err(EvaluationProofError::UnexpectedNormalForm {
            expected: left_normal,
            actual: right_normal,
        });
    }

    let left_proof =
        proof_by_evaluation_to_computation_in_theory(left, left_normal, theory, limit)?;
    let right_proof =
        proof_by_evaluation_to_computation_in_theory(right, right_normal, theory, limit)?;

    Ok(Proof::Trans(
        Box::new(left_proof),
        Box::new(Proof::Symm(Box::new(right_proof))),
    ))
}

pub(super) fn check_evaluates_to_in_theory(
    computation: Computation,
    outcome: impl Into<Outcome>,
    proof: &Proof,
    theory: &Theory,
) -> bool {
    theory.check(proof, &computes_to_outcome(computation, outcome))
}
