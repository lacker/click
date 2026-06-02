//! Proof-script elaboration and evaluation-proof helpers.

use crate::{
    Computation, Name, Outcome, Proof, Step, Theorem, TheoremError, Theory, alpha_eq_computation,
    computes_to_outcome,
};

use super::source::{ParseError, ParsedModule, ParsedTheorem, ProofExpr, ProofScript};

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofElaborationError {
    EvaluationFailed(EvaluationProofError),
    UnknownTheorem(Name),
    InSubproof {
        form: &'static str,
        error: Box<ProofElaborationError>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceTheoremError {
    ModuleParseFailed(ParseError),
    ProofElaborationFailed {
        theorem: Name,
        error: ProofElaborationError,
    },
    RequestedTheoremMissing {
        theorem: Name,
    },
    TheoremRejected {
        theorem: Name,
        error: TheoremError,
    },
}

pub(crate) fn define_source_theorem(
    theorem: &ParsedTheorem,
    theory: &mut Theory,
) -> Result<Theorem, SourceTheoremError> {
    let proof = proof_for_theorem_result(theorem, theory)?;
    theory
        .define_theorem_from_proof_result(theorem.name, proof, theorem.prop.clone())
        .map_err(|error| SourceTheoremError::TheoremRejected {
            theorem: theorem.name,
            error,
        })
}

pub(crate) fn proof_for_theorem_result(
    theorem: &ParsedTheorem,
    theory: &Theory,
) -> Result<Proof, SourceTheoremError> {
    match &theorem.proof {
        ProofScript::Proof(proof) => proof_expr_to_proof(proof, theory).map_err(|error| {
            SourceTheoremError::ProofElaborationFailed {
                theorem: theorem.name,
                error,
            }
        }),
    }
}

pub(crate) fn source_theorem_result(
    module: ParsedModule,
    name: Name,
    mut theory: Theory,
) -> Result<Theorem, SourceTheoremError> {
    for theorem in module.theorems {
        let requested = theorem.name == name;
        let theorem = define_source_theorem(&theorem, &mut theory)?;

        if requested {
            return Ok(theorem);
        }
    }

    Err(SourceTheoremError::RequestedTheoremMissing { theorem: name })
}

fn proof_expr_to_proof(proof: &ProofExpr, theory: &Theory) -> Result<Proof, ProofElaborationError> {
    match proof {
        ProofExpr::Known(name) => {
            if theory.theorem(*name).is_some() {
                Ok(Proof::Known(*name))
            } else {
                Err(ProofElaborationError::UnknownTheorem(*name))
            }
        }
        ProofExpr::Assume(symbol) => Ok(Proof::Assume(*symbol)),
        ProofExpr::Symm(proof) => Ok(Proof::Symm(Box::new(subproof("symm", proof, theory)?))),
        ProofExpr::Trans(first, second) => Ok(Proof::Trans(
            Box::new(subproof("trans first", first, theory)?),
            Box::new(subproof("trans second", second, theory)?),
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
        .map_err(ProofElaborationError::EvaluationFailed),
        ProofExpr::EvalSame { left, right, limit } => {
            proof_by_same_normal_form_in_theory(left.clone(), right.clone(), theory, *limit)
                .map_err(ProofElaborationError::EvaluationFailed)
        }
        ProofExpr::Rewrite {
            equality,
            proof,
            variable,
            template,
        } => Ok(Proof::Rewrite {
            equality: Box::new(subproof("rewrite equality", equality, theory)?),
            proof: Box::new(subproof("rewrite proof", proof, theory)?),
            variable: *variable,
            template: template.clone(),
        }),
        ProofExpr::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => Ok(Proof::ImpliesIntro {
            assumption: *assumption,
            premise: premise.clone(),
            proof: Box::new(subproof("implies-intro proof", proof, theory)?),
        }),
        ProofExpr::ImpliesElim {
            implication,
            premise,
        } => Ok(Proof::ImpliesElim {
            implication: Box::new(subproof("implies-elim implication", implication, theory)?),
            premise: Box::new(subproof("implies-elim premise", premise, theory)?),
        }),
        ProofExpr::ExistsIntro {
            variable,
            guard,
            body,
            witness,
            proof,
        } => Ok(Proof::ExistsIntro {
            variable: *variable,
            guard: guard.clone(),
            body: body.clone(),
            witness: witness.clone(),
            proof: Box::new(subproof("exists-intro proof", proof, theory)?),
        }),
        ProofExpr::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        } => Ok(Proof::ExistsElim {
            existential: Box::new(subproof("exists-elim existential", existential, theory)?),
            witness: *witness,
            assumption: *assumption,
            proof: Box::new(subproof("exists-elim proof", proof, theory)?),
        }),
        ProofExpr::AndIntro(left, right) => Ok(Proof::AndIntro(
            Box::new(subproof("and-intro left", left, theory)?),
            Box::new(subproof("and-intro right", right, theory)?),
        )),
        ProofExpr::AndElimLeft(proof) => Ok(Proof::AndElimLeft(Box::new(subproof(
            "and-elim-left",
            proof,
            theory,
        )?))),
        ProofExpr::AndElimRight(proof) => Ok(Proof::AndElimRight(Box::new(subproof(
            "and-elim-right",
            proof,
            theory,
        )?))),
        ProofExpr::ListInduction {
            variable,
            property,
            base,
            head,
            tail,
            induction_hypothesis_assumption,
            step,
        } => Ok(Proof::ListInduction {
            variable: *variable,
            property: property.clone(),
            base: Box::new(subproof("list-induction base", base, theory)?),
            head: *head,
            tail: *tail,
            induction_hypothesis_assumption: *induction_hypothesis_assumption,
            step: Box::new(subproof("list-induction step", step, theory)?),
        }),
        ProofExpr::ForAllIntro {
            variable,
            guard,
            proof,
        } => Ok(Proof::ForAllIntro {
            variable: *variable,
            guard: guard.clone(),
            proof: Box::new(subproof("forall-intro proof", proof, theory)?),
        }),
        ProofExpr::ForAllElim { forall, argument } => Ok(Proof::ForAllElim {
            forall: Box::new(subproof("forall-elim forall", forall, theory)?),
            argument: argument.clone(),
        }),
    }
}

fn subproof(
    form: &'static str,
    proof: &ProofExpr,
    theory: &Theory,
) -> Result<Proof, ProofElaborationError> {
    proof_expr_to_proof(proof, theory).map_err(|error| ProofElaborationError::InSubproof {
        form,
        error: Box::new(error),
    })
}

pub(crate) fn evaluation_chain_in_theory(
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

pub(crate) fn proof_by_evaluation_in_theory(
    computation: Computation,
    expected: impl Into<Outcome>,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    proof_by_evaluation_to_computation_in_theory(computation, expected.into().into(), theory, limit)
}

pub(crate) fn proof_by_evaluation_to_computation_in_theory(
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

pub(crate) fn proof_by_reduction_in_theory(
    computation: Computation,
    expected: impl Into<Outcome>,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    proof_by_reduction_to_computation_in_theory(computation, expected.into().into(), theory, limit)
}

pub(crate) fn proof_by_reduction_to_computation_in_theory(
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

pub(crate) fn proof_by_same_normal_form_in_theory(
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

pub(crate) fn check_evaluates_to_in_theory(
    computation: Computation,
    outcome: impl Into<Outcome>,
    proof: &Proof,
    theory: &Theory,
) -> bool {
    theory.check(proof, &computes_to_outcome(computation, outcome))
}
