//! Proof-script elaboration and evaluation-proof helpers.

use std::collections::HashSet;

use crate::{
    Computation, Context, ListCase, Name, Proof, Prop, Step, Symbol, Theorem, TheoremError, Theory,
    alpha_eq_computation, alpha_eq_prop, free_symbols, is_list, is_value, substitute_prop,
};

#[cfg(test)]
use crate::{Outcome, computes_to_outcome};

#[cfg(test)]
use super::source::ParsedModule;
use super::source::{
    CalcStep, ParseError, ParsedTheorem, ProofExpr, ProofScript, TacticExpr, TacticScript,
};

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
        ProofScript::By(script) => {
            tactic_script_to_proof(script, theory, &Goal::new(theorem.prop.clone())).map_err(
                |error| SourceTheoremError::ProofElaborationFailed {
                    theorem: theorem.name,
                    error,
                },
            )
        }
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

fn proof_expr_to_proof(proof: &ProofExpr, theory: &Theory) -> Result<Proof, ProofElaborationError> {
    proof_expr_to_proof_in_context(proof, theory, &Context::new())
}

fn proof_expr_to_proof_in_context(
    proof: &ProofExpr,
    theory: &Theory,
    context: &Context,
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
        ProofExpr::Symm(proof) => Ok(Proof::Symm(Box::new(subproof(
            "symm", proof, theory, context,
        )?))),
        ProofExpr::Trans(first, second) => Ok(Proof::Trans(
            Box::new(subproof("trans first", first, theory, context)?),
            Box::new(subproof("trans second", second, theory, context)?),
        )),
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
            equality: Box::new(subproof("rewrite equality", equality, theory, context)?),
            proof: Box::new(subproof("rewrite proof", proof, theory, context)?),
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
                proof: Box::new(subproof("implies-intro proof", proof, theory, &context)?),
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
            )?),
            premise: Box::new(subproof("implies-elim premise", premise, theory, context)?),
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
            proof: Box::new(subproof("exists-intro proof", proof, theory, context)?),
        }),
        ProofExpr::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        } => {
            let existential_proof =
                subproof("exists-elim existential", existential, theory, context)?;
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
                proof: Box::new(subproof("exists-elim proof", proof, theory, &context)?),
            })
        }
        ProofExpr::AndIntro(left, right) => Ok(Proof::AndIntro(
            Box::new(subproof("and-intro left", left, theory, context)?),
            Box::new(subproof("and-intro right", right, theory, context)?),
        )),
        ProofExpr::AndElimLeft(proof) => Ok(Proof::AndElimLeft(Box::new(subproof(
            "and-elim-left",
            proof,
            theory,
            context,
        )?))),
        ProofExpr::AndElimRight(proof) => Ok(Proof::AndElimRight(Box::new(subproof(
            "and-elim-right",
            proof,
            theory,
            context,
        )?))),
        ProofExpr::OrIntroLeft { proof, right } => Ok(Proof::OrIntroLeft {
            proof: Box::new(subproof("or-intro-left", proof, theory, context)?),
            right: right.clone(),
        }),
        ProofExpr::OrIntroRight { left, proof } => Ok(Proof::OrIntroRight {
            left: left.clone(),
            proof: Box::new(subproof("or-intro-right", proof, theory, context)?),
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
            )?),
            left_assumption: *left_assumption,
            left_proof: Box::new(subproof("or-elim left", left_proof, theory, context)?),
            right_assumption: *right_assumption,
            right_proof: Box::new(subproof("or-elim right", right_proof, theory, context)?),
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
            base: Box::new(subproof("list-induction base", base, theory, context)?),
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
            )?),
        }),
        ProofExpr::ForAllIntro {
            variable,
            guard,
            proof,
        } => {
            let mut context = context.clone();
            if let Some(guard) = guard {
                context.insert(*variable, guard.clone());
            }
            Ok(Proof::ForAllIntro {
                variable: *variable,
                guard: guard.clone(),
                proof: Box::new(subproof("forall-intro proof", proof, theory, &context)?),
            })
        }
        ProofExpr::ForAllElim { forall, argument } => Ok(Proof::ForAllElim {
            forall: Box::new(subproof("forall-elim forall", forall, theory, context)?),
            argument: argument.clone(),
        }),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Goal {
    context: Context,
    target: Prop,
}

impl Goal {
    fn new(target: Prop) -> Self {
        Self {
            context: Context::new(),
            target,
        }
    }
}

fn tactic_script_to_proof(
    script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    tactic_steps_to_proof(&script.tactics, theory, goal)
}

fn tactic_steps_to_proof(
    tactics: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Some((tactic, rest)) = tactics.split_first() else {
        return Err(tactic_failed("by", "tactic script left the goal unsolved"));
    };

    match tactic {
        TacticExpr::Intro(symbol) => tactic_intro(*symbol, rest, theory, goal),
        TacticExpr::Exact(proof) => {
            ensure_no_more_tactics(rest, "exact")?;
            tactic_exact(proof, theory, goal)
        }
        TacticExpr::Assumption => {
            ensure_no_more_tactics(rest, "assumption")?;
            tactic_assumption(goal)
        }
        TacticExpr::Eval { limit } => {
            ensure_no_more_tactics(rest, "eval")?;
            tactic_eval(*limit, theory, goal)
        }
        TacticExpr::Apply { theorem, arguments } => {
            ensure_no_more_tactics(rest, "apply")?;
            tactic_apply(*theorem, arguments, theory, goal)
        }
        TacticExpr::Split { left, right } => {
            ensure_no_more_tactics(rest, "split")?;
            tactic_split(left, right, theory, goal)
        }
        TacticExpr::Exists { witness, proof } => {
            ensure_no_more_tactics(rest, "exists")?;
            tactic_exists(witness, proof, theory, goal)
        }
        TacticExpr::ExistsElim {
            existential,
            witness,
            assumption,
        } => tactic_exists_elim(existential, *witness, *assumption, rest, theory, goal),
        TacticExpr::ForAllElim { forall, arguments } => {
            ensure_no_more_tactics(rest, "forall-elim")?;
            tactic_forall_elim(forall, arguments, theory, goal)
        }
        TacticExpr::Left(proof) => {
            ensure_no_more_tactics(rest, "left")?;
            tactic_left(proof, theory, goal)
        }
        TacticExpr::Right(proof) => {
            ensure_no_more_tactics(rest, "right")?;
            tactic_right(proof, theory, goal)
        }
        TacticExpr::Rewrite { equality } => tactic_rewrite(equality, rest, theory, goal),
        TacticExpr::ListInduction {
            variable,
            base,
            head,
            tail,
            induction_hypothesis_assumption,
            step,
        } => {
            ensure_no_more_tactics(rest, "list-induction")?;
            tactic_list_induction(
                *variable,
                base,
                *head,
                *tail,
                *induction_hypothesis_assumption,
                step,
                theory,
                goal,
            )
        }
        TacticExpr::Calc { start, steps } => {
            ensure_no_more_tactics(rest, "calc")?;
            tactic_calc(start, steps, theory, goal)
        }
    }
}

fn tactic_intro(
    symbol: Symbol,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    match &goal.target {
        Prop::ForAll {
            variable,
            guard,
            body,
        } if *variable == symbol => {
            let mut next_goal = Goal {
                context: goal.context.clone(),
                target: body.as_ref().clone(),
            };
            if let Some(guard) = guard.as_ref() {
                next_goal.context.insert(symbol, guard.as_ref().clone());
            }
            Ok(Proof::ForAllIntro {
                variable: symbol,
                guard: guard.as_deref().cloned(),
                proof: Box::new(tactic_steps_to_proof(rest, theory, &next_goal)?),
            })
        }
        Prop::ForAll { variable, .. } => Err(tactic_failed(
            "intro",
            format!("expected theorem binder {:?}, got {:?}", variable, symbol),
        )),
        Prop::Implies(premise, conclusion) => {
            let mut next_goal = Goal {
                context: goal.context.clone(),
                target: conclusion.as_ref().clone(),
            };
            next_goal.context.insert(symbol, premise.as_ref().clone());
            Ok(Proof::ImpliesIntro {
                assumption: symbol,
                premise: premise.as_ref().clone(),
                proof: Box::new(tactic_steps_to_proof(rest, theory, &next_goal)?),
            })
        }
        _ => Err(tactic_failed(
            "intro",
            "goal is not a forall or implication",
        )),
    }
}

fn tactic_exact(
    proof_expr: &ProofExpr,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let proof = proof_expr_to_proof_in_context(proof_expr, theory, &goal.context)?;
    let Some(proven) = theory.proven_prop_in_context(&proof, &goal.context) else {
        return Err(tactic_failed(
            "exact",
            "proof expression proves no proposition",
        ));
    };

    if alpha_eq_prop(&proven, &goal.target) {
        Ok(proof)
    } else {
        Err(tactic_failed(
            "exact",
            format!("proof proves {:?}, but goal is {:?}", proven, goal.target),
        ))
    }
}

fn tactic_assumption(goal: &Goal) -> Result<Proof, ProofElaborationError> {
    goal.context
        .iter()
        .find_map(|(symbol, prop)| {
            alpha_eq_prop(prop, &goal.target).then_some(Proof::Assume(*symbol))
        })
        .ok_or_else(|| tactic_failed("assumption", "no local assumption matches the goal"))
}

fn tactic_eval(limit: usize, theory: &Theory, goal: &Goal) -> Result<Proof, ProofElaborationError> {
    let Prop::Equal(left, right) = &goal.target else {
        return Err(tactic_failed("eval", "goal is not an equality"));
    };

    proof_by_reduction_to_computation_in_theory_and_context(
        left.clone(),
        right.clone(),
        theory,
        &goal.context,
        limit,
    )
    .or_else(|_| {
        proof_by_same_normal_form_in_theory_and_context(
            left.clone(),
            right.clone(),
            theory,
            &goal.context,
            limit,
        )
    })
    .map_err(ProofElaborationError::EvaluationFailed)
}

fn tactic_apply(
    theorem: Name,
    arguments: &[Computation],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Some(mut prop) = theory.theorem(theorem).cloned() else {
        return Err(ProofElaborationError::UnknownTheorem(theorem));
    };
    let mut proof = Proof::Known(theorem);

    (proof, prop) = instantiate_forall("apply", proof, prop, arguments)?;

    apply_implications_from_context("apply", proof, prop, theory, goal)
}

fn instantiate_forall(
    tactic: &'static str,
    mut proof: Proof,
    mut prop: Prop,
    arguments: &[Computation],
) -> Result<(Proof, Prop), ProofElaborationError> {
    for argument in arguments {
        let Prop::ForAll { variable, body, .. } = prop else {
            return Err(tactic_failed(tactic, "too many explicit arguments"));
        };
        proof = Proof::ForAllElim {
            forall: Box::new(proof),
            argument: argument.clone(),
        };
        prop = substitute_prop(&body, variable, argument);
    }

    Ok((proof, prop))
}

fn apply_implications_from_context(
    tactic: &'static str,
    mut proof: Proof,
    mut prop: Prop,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    loop {
        if alpha_eq_prop(&prop, &goal.target) {
            return Ok(proof);
        }

        let Prop::Implies(premise, conclusion) = prop else {
            return Err(tactic_failed(
                tactic,
                format!("proof concludes {:?}, but goal is {:?}", prop, goal.target),
            ));
        };

        let premise_goal = Goal {
            context: goal.context.clone(),
            target: premise.as_ref().clone(),
        };
        let premise_proof = tactic_assumption(&premise_goal).map_err(|_| {
            tactic_failed(
                tactic,
                format!("premise {:?} is not available as an assumption", premise),
            )
        })?;

        proof = Proof::ImpliesElim {
            implication: Box::new(proof),
            premise: Box::new(premise_proof),
        };
        prop = theory
            .proven_prop_in_context(&proof, &goal.context)
            .ok_or_else(|| tactic_failed(tactic, "applying proof produced no proposition"))?;

        if alpha_eq_prop(&prop, conclusion.as_ref()) {
            prop = conclusion.as_ref().clone();
        }
    }
}

fn tactic_split(
    left_script: &TacticScript,
    right_script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Prop::And(left, right) = &goal.target else {
        return Err(tactic_failed("split", "goal is not a conjunction"));
    };

    Ok(Proof::AndIntro(
        Box::new(tactic_script_to_proof(
            left_script,
            theory,
            &Goal {
                context: goal.context.clone(),
                target: left.as_ref().clone(),
            },
        )?),
        Box::new(tactic_script_to_proof(
            right_script,
            theory,
            &Goal {
                context: goal.context.clone(),
                target: right.as_ref().clone(),
            },
        )?),
    ))
}

fn tactic_exists(
    witness: &Computation,
    script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Exists {
        variable,
        guard,
        body,
    } = &goal.target
    else {
        return Err(tactic_failed("exists", "goal is not an existential"));
    };

    let witness_goal = Goal {
        context: goal.context.clone(),
        target: substitute_prop(body, *variable, witness),
    };

    Ok(Proof::ExistsIntro {
        variable: *variable,
        guard: guard.as_deref().cloned(),
        body: body.as_ref().clone(),
        witness: witness.clone(),
        proof: Box::new(tactic_script_to_proof(script, theory, &witness_goal)?),
    })
}

fn tactic_exists_elim(
    existential_expr: &ProofExpr,
    witness: Symbol,
    assumption: Symbol,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let existential = proof_expr_to_proof_in_context(existential_expr, theory, &goal.context)?;
    let context = exists_elim_context(
        "exists-elim",
        &goal.context,
        theory,
        &existential,
        witness,
        assumption,
    )?;

    Ok(Proof::ExistsElim {
        existential: Box::new(existential),
        witness,
        assumption,
        proof: Box::new(tactic_steps_to_proof(
            rest,
            theory,
            &Goal {
                context,
                target: goal.target.clone(),
            },
        )?),
    })
}

fn tactic_forall_elim(
    forall_expr: &ProofExpr,
    arguments: &[Computation],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let proof = proof_expr_to_proof_in_context(forall_expr, theory, &goal.context)?;
    let prop = theory
        .proven_prop_in_context(&proof, &goal.context)
        .ok_or_else(|| tactic_failed("forall-elim", "proof proves no proposition"))?;
    let (proof, prop) = instantiate_forall("forall-elim", proof, prop, arguments)?;

    apply_implications_from_context("forall-elim", proof, prop, theory, goal)
}

fn tactic_left(
    script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Or(left, right) = &goal.target else {
        return Err(tactic_failed("left", "goal is not a disjunction"));
    };

    Ok(Proof::OrIntroLeft {
        proof: Box::new(tactic_script_to_proof(
            script,
            theory,
            &Goal {
                context: goal.context.clone(),
                target: left.as_ref().clone(),
            },
        )?),
        right: right.as_ref().clone(),
    })
}

fn tactic_right(
    script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Or(left, right) = &goal.target else {
        return Err(tactic_failed("right", "goal is not a disjunction"));
    };

    Ok(Proof::OrIntroRight {
        left: left.as_ref().clone(),
        proof: Box::new(tactic_script_to_proof(
            script,
            theory,
            &Goal {
                context: goal.context.clone(),
                target: right.as_ref().clone(),
            },
        )?),
    })
}

fn tactic_rewrite(
    equality_expr: &ProofExpr,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let equality = proof_expr_to_proof_in_context(equality_expr, theory, &goal.context)?;
    let Some(Prop::Equal(left, right)) = theory.proven_prop_in_context(&equality, &goal.context)
    else {
        return Err(tactic_failed("rewrite", "proof is not an equality"));
    };

    let placeholder = fresh_rewrite_symbol(&goal.target, &left, &right);
    let Some(template) = rewrite_template(&goal.target, &left, placeholder) else {
        return Err(tactic_failed(
            "rewrite",
            format!("goal does not contain the left side {:?}", left),
        ));
    };

    let rewritten_goal = Goal {
        context: goal.context.clone(),
        target: substitute_prop(&template, placeholder, &right),
    };
    let proof = tactic_steps_to_proof(rest, theory, &rewritten_goal)?;

    Ok(Proof::Rewrite {
        equality: Box::new(Proof::Symm(Box::new(equality))),
        proof: Box::new(proof),
        variable: placeholder,
        template,
    })
}

fn tactic_list_induction(
    variable: Symbol,
    base: &TacticScript,
    head: Symbol,
    tail: Symbol,
    induction_hypothesis_assumption: Symbol,
    step: &TacticScript,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Prop::ForAll {
        variable: goal_variable,
        guard: Some(guard),
        body,
    } = &goal.target
    else {
        return Err(tactic_failed(
            "list-induction",
            "goal is not a guarded forall",
        ));
    };

    if variable != *goal_variable {
        return Err(tactic_failed(
            "list-induction",
            format!(
                "expected theorem binder {:?}, got {:?}",
                goal_variable, variable
            ),
        ));
    }

    let expected_guard = is_list(Computation::Var(variable));
    if !alpha_eq_prop(guard, &expected_guard) {
        return Err(tactic_failed(
            "list-induction",
            "forall guard is not an is-list guard",
        ));
    }

    let property = body.as_ref().clone();
    let base_goal = Goal {
        context: goal.context.clone(),
        target: substitute_prop(&property, variable, &Computation::Nil),
    };
    let step_goal = Goal {
        context: list_induction_step_context(
            &goal.context,
            variable,
            &property,
            head,
            tail,
            induction_hypothesis_assumption,
        ),
        target: substitute_prop(
            &property,
            variable,
            &Computation::Cons {
                head: Box::new(Computation::Var(head)),
                tail: Box::new(Computation::Var(tail)),
            },
        ),
    };

    Ok(Proof::ListInduction {
        variable,
        property,
        base: Box::new(tactic_script_to_proof(base, theory, &base_goal)?),
        head,
        tail,
        induction_hypothesis_assumption,
        step: Box::new(tactic_script_to_proof(step, theory, &step_goal)?),
    })
}

fn tactic_calc(
    start: &Computation,
    steps: &[CalcStep],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Equal(goal_left, goal_right) = &goal.target else {
        return Err(tactic_failed("calc", "goal is not an equality"));
    };

    if !alpha_eq_computation(start, goal_left) {
        return Err(tactic_failed(
            "calc",
            format!(
                "calc starts at {:?}, but goal starts at {:?}",
                start, goal_left
            ),
        ));
    }

    let mut previous = start.clone();
    let mut proofs = Vec::new();

    for step in steps {
        let step_goal = Goal {
            context: goal.context.clone(),
            target: Prop::Equal(previous.clone(), step.target.clone()),
        };
        proofs.push(proof_script_to_proof_for_goal(
            &step.proof,
            theory,
            &step_goal,
        )?);
        previous = step.target.clone();
    }

    if !alpha_eq_computation(&previous, goal_right) {
        return Err(tactic_failed(
            "calc",
            format!(
                "calc ends at {:?}, but goal ends at {:?}",
                previous, goal_right
            ),
        ));
    }

    trans_chain(proofs).ok_or_else(|| tactic_failed("calc", "calc has no steps"))
}

fn proof_script_to_proof_for_goal(
    script: &ProofScript,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    match script {
        ProofScript::Proof(proof) => tactic_exact(proof, theory, goal),
        ProofScript::By(script) => tactic_script_to_proof(script, theory, goal),
    }
}

fn trans_chain(proofs: Vec<Proof>) -> Option<Proof> {
    let mut proofs = proofs.into_iter();
    let mut proof = proofs.next()?;

    for next in proofs {
        proof = Proof::Trans(Box::new(proof), Box::new(next));
    }

    Some(proof)
}

fn ensure_no_more_tactics(
    rest: &[TacticExpr],
    tactic: &'static str,
) -> Result<(), ProofElaborationError> {
    if rest.is_empty() {
        Ok(())
    } else {
        Err(tactic_failed(
            tactic,
            "tactic solved the current goal before the script ended",
        ))
    }
}

fn tactic_failed(tactic: &'static str, message: impl Into<String>) -> ProofElaborationError {
    ProofElaborationError::TacticFailed {
        tactic,
        message: message.into(),
    }
}

fn fresh_rewrite_symbol(target: &Prop, left: &Computation, right: &Computation) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols_prop(target, &mut symbols);
    add_all_symbols_computation(left, &mut symbols);
    add_all_symbols_computation(right, &mut symbols);

    let mut symbol = Symbol(0);
    while symbols.contains(&symbol) {
        symbol = Symbol(symbol.0 + 1);
    }
    symbol
}

fn rewrite_template(target: &Prop, needle: &Computation, placeholder: Symbol) -> Option<Prop> {
    let replacement = Computation::Var(placeholder);
    replace_first_prop(target, needle, &replacement)
}

fn replace_first_prop(
    prop: &Prop,
    needle: &Computation,
    replacement: &Computation,
) -> Option<Prop> {
    match prop {
        Prop::Equal(left, right) => replace_first_computation(left, needle, replacement)
            .map(|left| Prop::Equal(left, right.clone()))
            .or_else(|| {
                replace_first_computation(right, needle, replacement)
                    .map(|right| Prop::Equal(left.clone(), right))
            }),
        Prop::IsValue(computation) => {
            replace_first_computation(computation, needle, replacement).map(Prop::IsValue)
        }
        Prop::IsList(computation) => {
            replace_first_computation(computation, needle, replacement).map(Prop::IsList)
        }
        Prop::IsEffect(computation) => {
            replace_first_computation(computation, needle, replacement).map(Prop::IsEffect)
        }
        Prop::IsOutcome(computation) => {
            replace_first_computation(computation, needle, replacement).map(Prop::IsOutcome)
        }
        Prop::Implies(premise, conclusion) => replace_first_prop(premise, needle, replacement)
            .map(|premise| Prop::Implies(Box::new(premise), conclusion.clone()))
            .or_else(|| {
                replace_first_prop(conclusion, needle, replacement)
                    .map(|conclusion| Prop::Implies(premise.clone(), Box::new(conclusion)))
            }),
        Prop::And(left, right) => replace_first_prop(left, needle, replacement)
            .map(|left| Prop::And(Box::new(left), right.clone()))
            .or_else(|| {
                replace_first_prop(right, needle, replacement)
                    .map(|right| Prop::And(left.clone(), Box::new(right)))
            }),
        Prop::Or(left, right) => replace_first_prop(left, needle, replacement)
            .map(|left| Prop::Or(Box::new(left), right.clone()))
            .or_else(|| {
                replace_first_prop(right, needle, replacement)
                    .map(|right| Prop::Or(left.clone(), Box::new(right)))
            }),
        Prop::ForAll {
            variable,
            guard,
            body,
        } => replace_first_quantified_prop(
            QuantifiedProp::ForAll,
            *variable,
            guard,
            body,
            needle,
            replacement,
        ),
        Prop::Exists {
            variable,
            guard,
            body,
        } => replace_first_quantified_prop(
            QuantifiedProp::Exists,
            *variable,
            guard,
            body,
            needle,
            replacement,
        ),
    }
}

#[derive(Clone, Copy)]
enum QuantifiedProp {
    ForAll,
    Exists,
}

fn replace_first_quantified_prop(
    quantified: QuantifiedProp,
    variable: Symbol,
    guard: &Option<Box<Prop>>,
    body: &Prop,
    needle: &Computation,
    replacement: &Computation,
) -> Option<Prop> {
    if free_symbols(needle).contains(&variable) || free_symbols(replacement).contains(&variable) {
        return None;
    }

    let rebuild = |guard: Option<Box<Prop>>, body: Box<Prop>| match quantified {
        QuantifiedProp::ForAll => Prop::ForAll {
            variable,
            guard,
            body,
        },
        QuantifiedProp::Exists => Prop::Exists {
            variable,
            guard,
            body,
        },
    };

    guard
        .as_ref()
        .and_then(|guard| {
            replace_first_prop(guard, needle, replacement)
                .map(|guard| rebuild(Some(Box::new(guard)), Box::new(body.clone())))
        })
        .or_else(|| {
            replace_first_prop(body, needle, replacement)
                .map(|body| rebuild(guard.clone(), Box::new(body)))
        })
}

fn replace_first_computation(
    computation: &Computation,
    needle: &Computation,
    replacement: &Computation,
) -> Option<Computation> {
    if alpha_eq_computation(computation, needle) {
        return Some(replacement.clone());
    }

    match computation {
        Computation::Apply { function, argument } => {
            replace_first_computation(function, needle, replacement)
                .map(|function| Computation::Apply {
                    function: Box::new(function),
                    argument: argument.clone(),
                })
                .or_else(|| {
                    replace_first_computation(argument, needle, replacement).map(|argument| {
                        Computation::Apply {
                            function: function.clone(),
                            argument: Box::new(argument),
                        }
                    })
                })
        }
        Computation::Cons { head, tail } => replace_first_computation(head, needle, replacement)
            .map(|head| Computation::Cons {
                head: Box::new(head),
                tail: tail.clone(),
            })
            .or_else(|| {
                replace_first_computation(tail, needle, replacement).map(|tail| Computation::Cons {
                    head: head.clone(),
                    tail: Box::new(tail),
                })
            }),
        Computation::Head(computation) => {
            replace_first_computation(computation, needle, replacement)
                .map(|computation| Computation::Head(Box::new(computation)))
        }
        Computation::Tail(computation) => {
            replace_first_computation(computation, needle, replacement)
                .map(|computation| Computation::Tail(Box::new(computation)))
        }
        Computation::ListCase(list_case) => replace_first_list_case(list_case, needle, replacement),
        Computation::If {
            condition,
            then_branch,
            else_branch,
        } => replace_first_computation(condition, needle, replacement)
            .map(|condition| Computation::If {
                condition: Box::new(condition),
                then_branch: then_branch.clone(),
                else_branch: else_branch.clone(),
            })
            .or_else(|| {
                replace_first_computation(then_branch, needle, replacement).map(|then_branch| {
                    Computation::If {
                        condition: condition.clone(),
                        then_branch: Box::new(then_branch),
                        else_branch: else_branch.clone(),
                    }
                })
            })
            .or_else(|| {
                replace_first_computation(else_branch, needle, replacement).map(|else_branch| {
                    Computation::If {
                        condition: condition.clone(),
                        then_branch: then_branch.clone(),
                        else_branch: Box::new(else_branch),
                    }
                })
            }),
        Computation::SymbolEq { left, right } => {
            replace_first_computation(left, needle, replacement)
                .map(|left| Computation::SymbolEq {
                    left: Box::new(left),
                    right: right.clone(),
                })
                .or_else(|| {
                    replace_first_computation(right, needle, replacement).map(|right| {
                        Computation::SymbolEq {
                            left: left.clone(),
                            right: Box::new(right),
                        }
                    })
                })
        }
        Computation::ValueKind(computation) => {
            replace_first_computation(computation, needle, replacement)
                .map(|computation| Computation::ValueKind(Box::new(computation)))
        }
        Computation::Lambda(_)
        | Computation::Nil
        | Computation::Ref(_)
        | Computation::Error(_)
        | Computation::Diverge
        | Computation::Var(_)
        | Computation::Quote(_) => None,
    }
}

fn replace_first_list_case(
    list_case: &ListCase,
    needle: &Computation,
    replacement: &Computation,
) -> Option<Computation> {
    replace_first_computation(&list_case.list, needle, replacement)
        .map(|list| {
            let mut list_case = list_case.clone();
            list_case.list = Box::new(list);
            Computation::ListCase(list_case)
        })
        .or_else(|| {
            replace_first_computation(&list_case.nil, needle, replacement).map(|nil| {
                let mut list_case = list_case.clone();
                list_case.nil = Box::new(nil);
                Computation::ListCase(list_case)
            })
        })
}

fn add_all_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Equal(left, right) => {
            add_all_symbols_computation(left, symbols);
            add_all_symbols_computation(right, symbols);
        }
        Prop::IsValue(computation)
        | Prop::IsList(computation)
        | Prop::IsEffect(computation)
        | Prop::IsOutcome(computation) => {
            add_all_symbols_computation(computation, symbols);
        }
        Prop::Implies(premise, conclusion)
        | Prop::And(premise, conclusion)
        | Prop::Or(premise, conclusion) => {
            add_all_symbols_prop(premise, symbols);
            add_all_symbols_prop(conclusion, symbols);
        }
        Prop::ForAll {
            variable,
            guard,
            body,
        }
        | Prop::Exists {
            variable,
            guard,
            body,
        } => {
            symbols.insert(*variable);
            if let Some(guard) = guard {
                add_all_symbols_prop(guard, symbols);
            }
            add_all_symbols_prop(body, symbols);
        }
    }
}

fn add_all_symbols_computation(computation: &Computation, symbols: &mut HashSet<Symbol>) {
    match computation {
        Computation::Apply { function, argument } => {
            add_all_symbols_computation(function, symbols);
            add_all_symbols_computation(argument, symbols);
        }
        Computation::Lambda(lambda) => {
            symbols.insert(lambda.parameter);
            add_all_symbols_computation(&lambda.body, symbols);
        }
        Computation::Cons { head, tail } => {
            add_all_symbols_computation(head, symbols);
            add_all_symbols_computation(tail, symbols);
        }
        Computation::Head(computation)
        | Computation::Tail(computation)
        | Computation::ValueKind(computation) => add_all_symbols_computation(computation, symbols),
        Computation::ListCase(list_case) => {
            add_all_symbols_computation(&list_case.list, symbols);
            add_all_symbols_computation(&list_case.nil, symbols);
            symbols.insert(list_case.cons);
            add_all_symbols_computation(&list_case.cons_case, symbols);
        }
        Computation::If {
            condition,
            then_branch,
            else_branch,
        } => {
            add_all_symbols_computation(condition, symbols);
            add_all_symbols_computation(then_branch, symbols);
            add_all_symbols_computation(else_branch, symbols);
        }
        Computation::SymbolEq { left, right } => {
            add_all_symbols_computation(left, symbols);
            add_all_symbols_computation(right, symbols);
        }
        Computation::Var(symbol) | Computation::Quote(symbol) => {
            symbols.insert(*symbol);
        }
        Computation::Nil | Computation::Ref(_) | Computation::Error(_) | Computation::Diverge => {}
    }
}

fn list_induction_step_context(
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

fn exists_elim_context(
    tactic: &'static str,
    context: &Context,
    theory: &Theory,
    existential_proof: &Proof,
    witness: Symbol,
    assumption: Symbol,
) -> Result<Context, ProofElaborationError> {
    let mut context = context.clone();

    let Some(Prop::Exists {
        variable,
        guard,
        body,
    }) = theory.proven_prop_in_context(existential_proof, &context)
    else {
        return Err(tactic_failed(tactic, "proof is not an existential"));
    };

    let witness_var = Computation::Var(witness);
    if let Some(guard) = guard {
        context.insert(witness, substitute_prop(&guard, variable, &witness_var));
    }
    context.insert(assumption, substitute_prop(&body, variable, &witness_var));

    Ok(context)
}

fn subproof(
    form: &'static str,
    proof: &ProofExpr,
    theory: &Theory,
    context: &Context,
) -> Result<Proof, ProofElaborationError> {
    proof_expr_to_proof_in_context(proof, theory, context).map_err(|error| {
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
