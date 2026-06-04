//! Tactic-script elaboration into kernel proofs.

use std::collections::HashSet;

use crate::kernel::{primitive_prop_holds, structural_primitive_prop_holds};
use crate::{
    Computation, Context, ListCase, Name, Proof, Prop, Symbol, Theory, alpha_eq_computation,
    alpha_eq_prop, free_symbols, is_list, substitute_prop,
};

use super::proof::{
    ProofElaborationError, exists_elim_context, list_induction_step_context,
    proof_by_reduction_to_computation_in_theory_and_context,
    proof_by_same_normal_form_in_theory_and_context, proof_expr_to_proof_in_context,
    proof_expr_to_proof_in_context_with_target,
};
use super::source::{CalcStep, ProofExpr, ProofScript, TacticExpr, TacticScript};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Goal {
    context: Context,
    target: Prop,
}

impl Goal {
    pub(super) fn new(target: Prop) -> Self {
        Self {
            context: Context::new(),
            target,
        }
    }
}

pub(super) fn tactic_script_to_proof(
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
        TacticExpr::Have {
            assumption,
            prop,
            proof,
            body,
        } => {
            let rest = explicit_body_or_rest(body.as_ref(), rest, "have")?;
            tactic_have(*assumption, prop, proof, rest, theory, goal)
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
            body,
        } => {
            let rest = explicit_body_or_rest(body.as_ref(), rest, "exists-elim")?;
            tactic_exists_elim(existential, *witness, *assumption, rest, theory, goal)
        }
        TacticExpr::OrElim {
            disjunction,
            left_assumption,
            left,
            right_assumption,
            right,
        } => {
            ensure_no_more_tactics(rest, "or-elim")?;
            tactic_or_elim(
                disjunction,
                *left_assumption,
                left,
                *right_assumption,
                right,
                theory,
                goal,
            )
        }
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
        Prop::ForAll { variable, body } if *variable == symbol => {
            if let Prop::Implies(premise, conclusion) = body.as_ref() {
                let mut next_goal = Goal {
                    context: goal.context.clone(),
                    target: conclusion.as_ref().clone(),
                };
                next_goal.context.insert(symbol, premise.as_ref().clone());
                return Ok(Proof::ForAllIntro {
                    variable: symbol,
                    proof: Box::new(Proof::ImpliesIntro {
                        assumption: symbol,
                        premise: premise.as_ref().clone(),
                        proof: Box::new(tactic_steps_to_proof(rest, theory, &next_goal)?),
                    }),
                });
            }

            Ok(Proof::ForAllIntro {
                variable: symbol,
                proof: Box::new(tactic_steps_to_proof(
                    rest,
                    theory,
                    &Goal {
                        context: goal.context.clone(),
                        target: body.as_ref().clone(),
                    },
                )?),
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
    let proof = proof_expr_to_proof_in_context_with_target(
        proof_expr,
        theory,
        &goal.context,
        Some(&goal.target),
    )?;
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

fn tactic_have(
    assumption: Symbol,
    prop: &Prop,
    proof_script: &ProofScript,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    if goal.context.contains_key(&assumption) {
        return Err(tactic_failed(
            "have",
            format!("assumption symbol {:?} is already in scope", assumption),
        ));
    }

    let premise_proof = proof_script_to_proof_for_goal(
        proof_script,
        theory,
        &Goal {
            context: goal.context.clone(),
            target: prop.clone(),
        },
    )?;

    let mut context = goal.context.clone();
    context.insert(assumption, prop.clone());
    let implication = Proof::ImpliesIntro {
        assumption,
        premise: prop.clone(),
        proof: Box::new(tactic_steps_to_proof(
            rest,
            theory,
            &Goal {
                context,
                target: goal.target.clone(),
            },
        )?),
    };

    Ok(Proof::ImpliesElim {
        implication: Box::new(implication),
        premise: Box::new(premise_proof),
    })
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

    (proof, prop) = apply_arguments_and_implications(
        "apply",
        proof,
        prop,
        arguments,
        theory,
        &goal.context,
        Some(&goal.target),
    )?;

    if alpha_eq_prop(&prop, &goal.target) {
        Ok(proof)
    } else {
        Err(tactic_failed(
            "apply",
            format!("proof concludes {:?}, but goal is {:?}", prop, goal.target),
        ))
    }
}

pub(super) fn apply_arguments_and_implications(
    tactic: &'static str,
    mut proof: Proof,
    mut prop: Prop,
    arguments: &[Computation],
    theory: &Theory,
    context: &Context,
    target: Option<&Prop>,
) -> Result<(Proof, Prop), ProofElaborationError> {
    for argument in arguments {
        loop {
            match prop {
                Prop::ForAll { variable, body, .. } => {
                    let expected = substitute_prop(&body, variable, argument);
                    proof = Proof::ForAllElim {
                        forall: Box::new(proof),
                        argument: argument.clone(),
                    };
                    prop = theory
                        .proven_prop_in_context(&proof, context)
                        .ok_or_else(|| {
                            tactic_failed(tactic, "forall elimination produced no proposition")
                        })?;
                    if alpha_eq_prop(&prop, &expected) {
                        prop = expected;
                    }
                    break;
                }
                Prop::Implies(premise, conclusion) => {
                    proof = apply_available_premise(tactic, proof, premise.as_ref(), context)?;
                    prop = theory
                        .proven_prop_in_context(&proof, context)
                        .ok_or_else(|| {
                            tactic_failed(tactic, "applying premise produced no proposition")
                        })?;
                    if alpha_eq_prop(&prop, conclusion.as_ref()) {
                        prop = conclusion.as_ref().clone();
                    }
                }
                _ => return Err(tactic_failed(tactic, "too many explicit arguments")),
            }
        }
    }

    finish_implications(tactic, proof, prop, theory, context, target)
}

fn finish_implications(
    tactic: &'static str,
    mut proof: Proof,
    mut prop: Prop,
    theory: &Theory,
    context: &Context,
    target: Option<&Prop>,
) -> Result<(Proof, Prop), ProofElaborationError> {
    loop {
        if target.is_some_and(|target| alpha_eq_prop(&prop, target)) {
            return Ok((proof, prop));
        }

        let (premise, conclusion) = match &prop {
            Prop::Implies(premise, conclusion) => {
                (premise.as_ref().clone(), conclusion.as_ref().clone())
            }
            _ => {
                return match target {
                    Some(target) => Err(tactic_failed(
                        tactic,
                        format!("proof concludes {:?}, but goal is {:?}", prop, target),
                    )),
                    None => Ok((proof, prop)),
                };
            }
        };

        let next_proof = match target {
            Some(_) => apply_available_premise(tactic, proof.clone(), &premise, context),
            None => apply_structural_premise(tactic, proof.clone(), &premise, context),
        };
        let Ok(next_proof) = next_proof else {
            return match target {
                Some(_) => Err(tactic_failed(
                    tactic,
                    format!("premise {:?} is not available", premise),
                )),
                None => Ok((proof, prop)),
            };
        };

        proof = next_proof;
        prop = theory
            .proven_prop_in_context(&proof, context)
            .ok_or_else(|| tactic_failed(tactic, "applying premise produced no proposition"))?;

        if alpha_eq_prop(&prop, &conclusion) {
            prop = conclusion;
        }
    }
}

fn apply_available_premise(
    tactic: &'static str,
    implication: Proof,
    premise: &Prop,
    context: &Context,
) -> Result<Proof, ProofElaborationError> {
    let premise_proof = available_prop_proof(premise, context)
        .map_err(|_| tactic_failed(tactic, format!("premise {:?} is not available", premise)))?;

    Ok(Proof::ImpliesElim {
        implication: Box::new(implication),
        premise: Box::new(premise_proof),
    })
}

fn available_prop_proof(prop: &Prop, context: &Context) -> Result<Proof, ProofElaborationError> {
    let goal = Goal {
        context: context.clone(),
        target: prop.clone(),
    };
    tactic_assumption(&goal).or_else(|_| {
        primitive_prop_holds(prop, context)
            .then_some(Proof::Primitive(prop.clone()))
            .ok_or_else(|| tactic_failed("available", "proposition is not available"))
    })
}

fn apply_structural_premise(
    tactic: &'static str,
    implication: Proof,
    premise: &Prop,
    context: &Context,
) -> Result<Proof, ProofElaborationError> {
    if !structural_primitive_prop_holds(premise, context) {
        return Err(tactic_failed(
            tactic,
            format!("premise {:?} is not structurally available", premise),
        ));
    }

    Ok(Proof::ImpliesElim {
        implication: Box::new(implication),
        premise: Box::new(Proof::Primitive(premise.clone())),
    })
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
    let Prop::Exists { variable, body } = &goal.target else {
        return Err(tactic_failed("exists", "goal is not an existential"));
    };

    let (witness_goal, witness_predicate) =
        existential_witness_goal(body, *variable, witness, &goal.context);
    let proof = tactic_script_to_proof(
        script,
        theory,
        &Goal {
            context: goal.context.clone(),
            target: witness_goal,
        },
    )?;
    let proof = match witness_predicate {
        Some(witness_predicate) => Proof::AndIntro(
            Box::new(Proof::Primitive(witness_predicate)),
            Box::new(proof),
        ),
        None => proof,
    };

    Ok(Proof::ExistsIntro {
        variable: *variable,
        body: body.as_ref().clone(),
        witness: witness.clone(),
        proof: Box::new(proof),
    })
}

fn existential_witness_goal(
    body: &Prop,
    variable: Symbol,
    witness: &Computation,
    context: &Context,
) -> (Prop, Option<Prop>) {
    let Prop::And(left, right) = body else {
        return (substitute_prop(body, variable, witness), None);
    };

    let witness_predicate = substitute_prop(left, variable, witness);
    if primitive_prop_holds(&witness_predicate, context) {
        (
            substitute_prop(right, variable, witness),
            Some(witness_predicate),
        )
    } else {
        (substitute_prop(body, variable, witness), None)
    }
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

fn tactic_or_elim(
    disjunction_expr: &ProofExpr,
    left_assumption: Symbol,
    left_script: &TacticScript,
    right_assumption: Symbol,
    right_script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    if left_assumption == right_assumption {
        return Err(tactic_failed(
            "or-elim",
            "branch assumption symbols must be distinct",
        ));
    }
    if goal.context.contains_key(&left_assumption) || goal.context.contains_key(&right_assumption) {
        return Err(tactic_failed(
            "or-elim",
            "branch assumption symbol is already in scope",
        ));
    }

    let disjunction = proof_expr_to_proof_in_context(disjunction_expr, theory, &goal.context)?;
    let Some(Prop::Or(left, right)) = theory.proven_prop_in_context(&disjunction, &goal.context)
    else {
        return Err(tactic_failed("or-elim", "proof is not a disjunction"));
    };

    let mut left_context = goal.context.clone();
    left_context.insert(left_assumption, left.as_ref().clone());
    let mut right_context = goal.context.clone();
    right_context.insert(right_assumption, right.as_ref().clone());

    Ok(Proof::OrElim {
        disjunction: Box::new(disjunction),
        left_assumption,
        left_proof: Box::new(tactic_script_to_proof(
            left_script,
            theory,
            &Goal {
                context: left_context,
                target: goal.target.clone(),
            },
        )?),
        right_assumption,
        right_proof: Box::new(tactic_script_to_proof(
            right_script,
            theory,
            &Goal {
                context: right_context,
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
    let (proof, prop) = apply_arguments_and_implications(
        "forall-elim",
        proof,
        prop,
        arguments,
        theory,
        &goal.context,
        Some(&goal.target),
    )?;

    if alpha_eq_prop(&prop, &goal.target) {
        Ok(proof)
    } else {
        Err(tactic_failed(
            "forall-elim",
            format!("proof concludes {:?}, but goal is {:?}", prop, goal.target),
        ))
    }
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
    let (goal_variable, predicate, property) = list_induction_goal(&goal.target)?;

    if variable != goal_variable {
        return Err(tactic_failed(
            "list-induction",
            format!(
                "expected theorem binder {:?}, got {:?}",
                goal_variable, variable
            ),
        ));
    }

    let expected_predicate = is_list(Computation::Var(variable));
    if !alpha_eq_prop(&predicate, &expected_predicate) {
        return Err(tactic_failed(
            "list-induction",
            "forall predicate is not an is-list predicate",
        ));
    }

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

fn list_induction_goal(target: &Prop) -> Result<(Symbol, Prop, Prop), ProofElaborationError> {
    let Prop::ForAll { variable, body } = target else {
        return Err(tactic_failed("list-induction", "goal is not a forall"));
    };

    let Prop::Implies(predicate, body) = body.as_ref() else {
        return Err(tactic_failed(
            "list-induction",
            "forall body is not a predicate implication",
        ));
    };

    Ok((*variable, predicate.as_ref().clone(), body.as_ref().clone()))
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

fn explicit_body_or_rest<'a>(
    body: Option<&'a TacticScript>,
    rest: &'a [TacticExpr],
    tactic: &'static str,
) -> Result<&'a [TacticExpr], ProofElaborationError> {
    match body {
        Some(body) => {
            ensure_no_more_tactics(rest, tactic)?;
            Ok(&body.tactics)
        }
        None => Ok(rest),
    }
}

pub(super) fn tactic_failed(
    tactic: &'static str,
    message: impl Into<String>,
) -> ProofElaborationError {
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
        Prop::ForAll { variable, body } => replace_first_quantified_prop(
            QuantifiedProp::ForAll,
            *variable,
            body,
            needle,
            replacement,
        ),
        Prop::Exists { variable, body } => replace_first_quantified_prop(
            QuantifiedProp::Exists,
            *variable,
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
    body: &Prop,
    needle: &Computation,
    replacement: &Computation,
) -> Option<Prop> {
    if free_symbols(needle).contains(&variable) || free_symbols(replacement).contains(&variable) {
        return None;
    }

    let rebuild = |body: Box<Prop>| match quantified {
        QuantifiedProp::ForAll => Prop::ForAll { variable, body },
        QuantifiedProp::Exists => Prop::Exists { variable, body },
    };

    replace_first_prop(body, needle, replacement).map(|body| rebuild(Box::new(body)))
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
        Prop::ForAll { variable, body } | Prop::Exists { variable, body } => {
            symbols.insert(*variable);
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
