//! Proof-term elaboration and evaluation-proof helpers.

use crate::{
    Computation, Context, Name, Proof, Prop, Step, Symbol, Theorem, TheoremError, Theory,
    alpha_eq_computation, is_list, is_value, substitute_prop,
};

#[cfg(test)]
use crate::{Outcome, computes_to_outcome};

#[cfg(test)]
use super::source::ParsedModule;
use super::source::{ParseError, ParsedTheorem, PrettyEnv, ProofExpr, ProofScript, SourceSection};
use super::tactics::{self, Goal};

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
    TacticFailed {
        tactic: &'static str,
        message: String,
    },
    InSubproof {
        form: &'static str,
        error: Box<ProofElaborationError>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceTheoremError {
    ModuleParseFailed {
        section: Option<SourceSection>,
        error: ParseError,
    },
    ProofElaborationFailed {
        section: Option<SourceSection>,
        theorem: Name,
        error: ProofElaborationError,
    },
    RequestedTheoremMissing {
        theorem: Name,
    },
    TheoremRejected {
        section: Option<SourceSection>,
        theorem: Name,
        error: TheoremError,
    },
}

#[cfg(test)]
pub(crate) fn define_source_theorem(
    theorem: &ParsedTheorem,
    theory: &mut Theory,
) -> Result<Theorem, SourceTheoremError> {
    define_source_theorem_with_section(theorem, theory, None, &PrettyEnv::new())
}

pub(crate) fn define_source_theorem_with_section(
    theorem: &ParsedTheorem,
    theory: &mut Theory,
    section: Option<&SourceSection>,
    pretty: &PrettyEnv,
) -> Result<Theorem, SourceTheoremError> {
    let proof = proof_for_theorem_result_with_section(theorem, theory, section, pretty)?;
    theory
        .define_theorem_from_proof_result(theorem.name, proof, theorem.prop.clone())
        .map_err(|error| SourceTheoremError::TheoremRejected {
            section: section.cloned(),
            theorem: theorem.name,
            error,
        })
}

pub(crate) fn proof_for_theorem_result_with_section(
    theorem: &ParsedTheorem,
    theory: &Theory,
    section: Option<&SourceSection>,
    pretty: &PrettyEnv,
) -> Result<Proof, SourceTheoremError> {
    let pretty = pretty.with_theorem_locals(theorem);
    match &theorem.proof {
        ProofScript::Proof(proof) => proof_expr_to_proof(proof, theory, &pretty).map_err(|error| {
            SourceTheoremError::ProofElaborationFailed {
                section: section.cloned(),
                theorem: theorem.name,
                error,
            }
        }),
        ProofScript::By(script) => tactics::tactic_script_to_proof(
            script,
            theory,
            &Goal::new(theorem.prop.clone()),
            &pretty,
        )
        .map_err(|error| SourceTheoremError::ProofElaborationFailed {
            section: section.cloned(),
            theorem: theorem.name,
            error,
        }),
    }
}

#[cfg(test)]
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

fn proof_expr_to_proof(
    proof: &ProofExpr,
    theory: &Theory,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    proof_expr_to_proof_in_context(proof, theory, &Context::new(), pretty)
}

pub(super) fn proof_expr_to_proof_in_context(
    proof: &ProofExpr,
    theory: &Theory,
    context: &Context,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    proof_expr_to_proof_in_context_with_target(proof, theory, context, None, pretty)
}

pub(super) fn proof_expr_to_proof_in_context_with_target(
    proof: &ProofExpr,
    theory: &Theory,
    context: &Context,
    target: Option<&Prop>,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    match proof {
        ProofExpr::Known(name) => {
            if theory.theorem(*name).is_some() {
                Ok(Proof::Known(*name))
            } else {
                Err(ProofElaborationError::UnknownTheorem(*name))
            }
        }
        ProofExpr::Assume(symbol) => Ok(Proof::Assume(*symbol)),
        ProofExpr::Primitive(prop) => Ok(Proof::Primitive(prop.clone())),
        ProofExpr::Symm(proof) => Ok(Proof::Symm(Box::new(subproof(
            "symm", proof, theory, context, pretty,
        )?))),
        ProofExpr::Trans(first, second) => Ok(Proof::Trans(
            Box::new(subproof("trans first", first, theory, context, pretty)?),
            Box::new(subproof("trans second", second, theory, context, pretty)?),
        )),
        ProofExpr::SymbolEqTrue(proof) => Ok(Proof::SymbolEqTrueElim(Box::new(subproof(
            "symbol-eq-true",
            proof,
            theory,
            context,
            pretty,
        )?))),
        ProofExpr::IfTrueCondition(proof) => Ok(Proof::IfTrueWithFalseElseCondition(Box::new(
            subproof("if-true-condition", proof, theory, context, pretty)?,
        ))),
        ProofExpr::IfTrueThen(proof) => Ok(Proof::IfTrueWithFalseElseThen(Box::new(subproof(
            "if-true-then",
            proof,
            theory,
            context,
            pretty,
        )?))),
        ProofExpr::IfEffectThenConditionFalse(proof) => Ok(
            Proof::IfValueWithEffectThenConditionFalse(Box::new(subproof(
                "if-effect-then-condition-false",
                proof,
                theory,
                context,
                pretty,
            )?)),
        ),
        ProofExpr::IfEffectThenElse(proof) => Ok(Proof::IfValueWithEffectThenElse(Box::new(
            subproof("if-effect-then-else", proof, theory, context, pretty)?,
        ))),
        ProofExpr::IfValueConditionBool(proof) => Ok(Proof::IfValueConditionBool(Box::new(
            subproof("if-value-condition-bool", proof, theory, context, pretty)?,
        ))),
        ProofExpr::DistinctOutcomes(proof) => Ok(Proof::DistinctOutcomes(Box::new(subproof(
            "distinct-outcomes",
            proof,
            theory,
            context,
            pretty,
        )?))),
        ProofExpr::ValueNonSymbolNonLambdaIsList {
            value,
            not_symbol,
            not_lambda,
        } => Ok(Proof::ValueNonSymbolNonLambdaIsList {
            value: Box::new(subproof(
                "value-non-symbol-non-lambda-is-list value",
                value,
                theory,
                context,
                pretty,
            )?),
            not_symbol: Box::new(subproof(
                "value-non-symbol-non-lambda-is-list not-symbol",
                not_symbol,
                theory,
                context,
                pretty,
            )?),
            not_lambda: Box::new(subproof(
                "value-non-symbol-non-lambda-is-list not-lambda",
                not_lambda,
                theory,
                context,
                pretty,
            )?),
        }),
        ProofExpr::AbsurdElim { absurd, prop } => Ok(Proof::AbsurdElim {
            absurd: Box::new(subproof("absurd-elim", absurd, theory, context, pretty)?),
            prop: prop.clone(),
        }),
        ProofExpr::EvalTo {
            computation,
            expected,
            limit,
        } => proof_by_reduction_to_computation_in_theory_and_context(
            computation.clone(),
            expected.clone(),
            theory,
            context,
            *limit,
        )
        .map_err(ProofElaborationError::EvaluationFailed),
        ProofExpr::EvalSame { left, right, limit } => {
            proof_by_same_normal_form_in_theory_and_context(
                left.clone(),
                right.clone(),
                theory,
                context,
                *limit,
            )
            .map_err(ProofElaborationError::EvaluationFailed)
        }
        ProofExpr::Rewrite {
            equality,
            proof,
            variable,
            template,
        } => Ok(Proof::Rewrite {
            equality: Box::new(subproof(
                "rewrite equality",
                equality,
                theory,
                context,
                pretty,
            )?),
            proof: Box::new(subproof("rewrite proof", proof, theory, context, pretty)?),
            variable: *variable,
            template: template.clone(),
        }),
        ProofExpr::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => {
            let mut context = context.clone();
            context.insert(*assumption, premise.clone());
            Ok(Proof::ImpliesIntro {
                assumption: *assumption,
                premise: premise.clone(),
                proof: Box::new(subproof(
                    "implies-intro proof",
                    proof,
                    theory,
                    &context,
                    pretty,
                )?),
            })
        }
        ProofExpr::ImpliesElim {
            implication,
            premise,
        } => Ok(Proof::ImpliesElim {
            implication: Box::new(subproof(
                "implies-elim implication",
                implication,
                theory,
                context,
                pretty,
            )?),
            premise: Box::new(subproof(
                "implies-elim premise",
                premise,
                theory,
                context,
                pretty,
            )?),
        }),
        ProofExpr::ExistsIntro {
            variable,
            body,
            witness,
            proof,
        } => Ok(Proof::ExistsIntro {
            variable: *variable,
            body: body.clone(),
            witness: witness.clone(),
            proof: Box::new(subproof(
                "exists-intro proof",
                proof,
                theory,
                context,
                pretty,
            )?),
        }),
        ProofExpr::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        } => {
            let existential_proof = subproof(
                "exists-elim existential",
                existential,
                theory,
                context,
                pretty,
            )?;
            let context = exists_elim_context(
                "exists-elim",
                context,
                theory,
                &existential_proof,
                *witness,
                *assumption,
            )?;

            Ok(Proof::ExistsElim {
                existential: Box::new(existential_proof),
                witness: *witness,
                assumption: *assumption,
                proof: Box::new(subproof(
                    "exists-elim proof",
                    proof,
                    theory,
                    &context,
                    pretty,
                )?),
            })
        }
        ProofExpr::AndIntro(left, right) => Ok(Proof::AndIntro(
            Box::new(subproof("and-intro left", left, theory, context, pretty)?),
            Box::new(subproof("and-intro right", right, theory, context, pretty)?),
        )),
        ProofExpr::AndElimLeft(proof) => Ok(Proof::AndElimLeft(Box::new(subproof(
            "and-elim-left",
            proof,
            theory,
            context,
            pretty,
        )?))),
        ProofExpr::AndElimRight(proof) => Ok(Proof::AndElimRight(Box::new(subproof(
            "and-elim-right",
            proof,
            theory,
            context,
            pretty,
        )?))),
        ProofExpr::OrIntroLeft { proof, right } => Ok(Proof::OrIntroLeft {
            proof: Box::new(subproof("or-intro-left", proof, theory, context, pretty)?),
            right: right.clone(),
        }),
        ProofExpr::OrIntroRight { left, proof } => Ok(Proof::OrIntroRight {
            left: left.clone(),
            proof: Box::new(subproof("or-intro-right", proof, theory, context, pretty)?),
        }),
        ProofExpr::OrElim {
            disjunction,
            left_assumption,
            left_proof,
            right_assumption,
            right_proof,
        } => Ok(Proof::OrElim {
            disjunction: Box::new(subproof(
                "or-elim disjunction",
                disjunction,
                theory,
                context,
                pretty,
            )?),
            left_assumption: *left_assumption,
            left_proof: Box::new(subproof(
                "or-elim left",
                left_proof,
                theory,
                context,
                pretty,
            )?),
            right_assumption: *right_assumption,
            right_proof: Box::new(subproof(
                "or-elim right",
                right_proof,
                theory,
                context,
                pretty,
            )?),
        }),
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
            base: Box::new(subproof(
                "list-induction base",
                base,
                theory,
                context,
                pretty,
            )?),
            head: *head,
            tail: *tail,
            induction_hypothesis_assumption: *induction_hypothesis_assumption,
            step: Box::new(subproof(
                "list-induction step",
                step,
                theory,
                &list_induction_step_context(
                    context,
                    *variable,
                    property,
                    *head,
                    *tail,
                    *induction_hypothesis_assumption,
                ),
                pretty,
            )?),
        }),
        ProofExpr::ForAllIntro { variable, proof } => Ok(Proof::ForAllIntro {
            variable: *variable,
            proof: Box::new(subproof(
                "forall-intro proof",
                proof,
                theory,
                context,
                pretty,
            )?),
        }),
        ProofExpr::ForAllElim { forall, argument } => {
            let proof = subproof("forall-elim forall", forall, theory, context, pretty)?;
            let prop = theory
                .proven_prop_in_context(&proof, context)
                .ok_or_else(|| {
                    tactics::tactic_failed("forall-elim", "proof proves no proposition")
                })?;
            tactics::apply_arguments_and_implications(
                "forall-elim",
                proof,
                prop,
                std::slice::from_ref(argument),
                theory,
                context,
                target,
                pretty,
                None,
                None,
            )
            .map(|(proof, _)| proof)
        }
        ProofExpr::Apply { proof, arguments } => {
            let proof = subproof("proof application", proof, theory, context, pretty)?;
            let prop = theory
                .proven_prop_in_context(&proof, context)
                .ok_or_else(|| {
                    tactics::tactic_failed("proof application", "proof proves no proposition")
                })?;
            tactics::apply_arguments_and_implications(
                "proof application",
                proof,
                prop,
                arguments,
                theory,
                context,
                target,
                pretty,
                None,
                None,
            )
            .map(|(proof, _)| proof)
        }
    }
}

pub(super) fn list_induction_step_context(
    context: &Context,
    variable: Symbol,
    property: &crate::Prop,
    head: Symbol,
    tail: Symbol,
    induction_hypothesis_assumption: Symbol,
) -> Context {
    let mut context = context.clone();
    let tail_var = Computation::Var(tail);
    context.insert(
        induction_hypothesis_assumption,
        substitute_prop(property, variable, &tail_var),
    );
    context.insert(head, is_value(Computation::Var(head)));
    context.insert(tail, is_list(tail_var));
    context
}

pub(super) fn exists_elim_context(
    tactic: &'static str,
    context: &Context,
    theory: &Theory,
    existential_proof: &Proof,
    witness: Symbol,
    assumption: Symbol,
) -> Result<Context, ProofElaborationError> {
    let mut context = context.clone();

    let Some(Prop::Exists { variable, body }) =
        theory.proven_prop_in_context(existential_proof, &context)
    else {
        return Err(tactics::tactic_failed(
            tactic,
            "proof is not an existential",
        ));
    };

    let witness_var = Computation::Var(witness);
    match body.as_ref() {
        Prop::And(left, right) => {
            context.insert(witness, substitute_prop(left, variable, &witness_var));
            context.insert(assumption, substitute_prop(right, variable, &witness_var));
        }
        _ => {
            context.insert(assumption, substitute_prop(&body, variable, &witness_var));
        }
    }

    Ok(context)
}

fn subproof(
    form: &'static str,
    proof: &ProofExpr,
    theory: &Theory,
    context: &Context,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    proof_expr_to_proof_in_context(proof, theory, context, pretty).map_err(|error| {
        ProofElaborationError::InSubproof {
            form,
            error: Box::new(error),
        }
    })
}

pub(crate) fn evaluation_chain_in_theory_and_context(
    computation: Computation,
    theory: &Theory,
    context: &Context,
    limit: usize,
) -> Result<Vec<Computation>, EvaluationProofError> {
    let mut computation = computation;
    let mut chain = vec![computation.clone()];

    for _ in 0..limit {
        match theory.reduce_in_context(&computation, context) {
            Step::Reduced(next) => {
                chain.push(next.clone());
                computation = next;
            }
            Step::Normal => return Ok(chain),
        }
    }

    Err(EvaluationProofError::StepLimitExceeded { limit })
}

#[cfg(test)]
pub(crate) fn proof_by_evaluation_in_theory(
    computation: Computation,
    expected: impl Into<Outcome>,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    proof_by_evaluation_to_computation_in_theory(computation, expected.into().into(), theory, limit)
}

#[cfg(test)]
pub(crate) fn proof_by_evaluation_to_computation_in_theory(
    computation: Computation,
    expected: Computation,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    proof_by_evaluation_to_computation_in_theory_and_context(
        computation,
        expected,
        theory,
        &Context::new(),
        limit,
    )
}

pub(crate) fn proof_by_evaluation_to_computation_in_theory_and_context(
    computation: Computation,
    expected: Computation,
    theory: &Theory,
    context: &Context,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let chain = evaluation_chain_in_theory_and_context(computation, theory, context, limit)?;
    let actual = chain
        .last()
        .cloned()
        .expect("evaluation chains are nonempty");

    if !alpha_eq_computation(&actual, &expected) {
        return Err(EvaluationProofError::UnexpectedNormalForm { expected, actual });
    }

    Ok(Proof::Steps(chain))
}

pub(crate) fn proof_by_reduction_to_computation_in_theory_and_context(
    computation: Computation,
    expected: Computation,
    theory: &Theory,
    context: &Context,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let mut computation = computation;
    let mut chain = vec![computation.clone()];

    if alpha_eq_computation(&computation, &expected) {
        return Ok(Proof::Steps(chain));
    }

    for _ in 0..limit {
        match theory.reduce_in_context(&computation, context) {
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

pub(crate) fn proof_by_same_normal_form_in_theory_and_context(
    left: Computation,
    right: Computation,
    theory: &Theory,
    context: &Context,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let left_normal = theory.normal_form_in_context(&left, context);
    let right_normal = theory.normal_form_in_context(&right, context);

    if !alpha_eq_computation(&left_normal, &right_normal) {
        return Err(EvaluationProofError::UnexpectedNormalForm {
            expected: left_normal,
            actual: right_normal,
        });
    }

    let left_proof = proof_by_evaluation_to_computation_in_theory_and_context(
        left,
        left_normal,
        theory,
        context,
        limit,
    )?;
    let right_proof = proof_by_evaluation_to_computation_in_theory_and_context(
        right,
        right_normal,
        theory,
        context,
        limit,
    )?;

    Ok(Proof::Trans(
        Box::new(left_proof),
        Box::new(Proof::Symm(Box::new(right_proof))),
    ))
}

#[cfg(test)]
pub(crate) fn check_evaluates_to_in_theory(
    computation: Computation,
    outcome: impl Into<Outcome>,
    proof: &Proof,
    theory: &Theory,
) -> bool {
    theory.check(proof, &computes_to_outcome(computation, outcome))
}
