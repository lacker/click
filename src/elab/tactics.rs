//! Tactic-script elaboration into kernel proofs.

use std::collections::HashSet;

use crate::kernel::{primitive_prop_holds, structural_primitive_prop_holds};
use crate::{
    Computation, LAMBDA_KIND_SYMBOL, ListCase, Name, Proof, ProofContext, Prop, SYMBOL_KIND_SYMBOL,
    Symbol, TRUE_SYMBOL, Theory, alpha_eq_computation, alpha_eq_prop, equal, free_symbols, is_list,
    is_value, substitute_prop, symbol_eq, value_kind,
};

use super::diagnostics::{
    compact_computation_source, compact_debug, compact_prop_source, computation_diagnostic,
    context_diagnostic, name_source, prop_diagnostic, symbol_source,
};
use super::proof::{
    ProofElaborationError, exists_elim_context, list_induction_step_context,
    proof_by_reduction_to_computation_in_theory_and_context,
    proof_by_same_normal_form_in_theory_and_context, proof_expr_to_proof_in_context,
    proof_expr_to_proof_in_context_with_target,
};
use super::simp::{tactic_simp, tactic_simpa};
use super::source::{CalcStep, PrettyEnv, ProofExpr, ProofScript, TacticExpr, TacticScript};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Goal {
    pub(super) context: ProofContext,
    pub(super) target: Prop,
}

impl Goal {
    pub(super) fn new(target: Prop) -> Self {
        Self {
            context: ProofContext::new(),
            target,
        }
    }
}

pub(super) fn tactic_script_to_proof(
    script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    tactic_steps_to_proof(&script.tactics, theory, goal, pretty)
}

fn tactic_steps_to_proof(
    tactics: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Some((tactic, rest)) = tactics.split_first() else {
        return Err(tactic_failed("by", "tactic script left the goal unsolved"));
    };

    let result = match tactic {
        TacticExpr::Intro(symbol) => tactic_intro(*symbol, rest, theory, goal, pretty),
        TacticExpr::Exact(proof) => {
            ensure_no_more_tactics(rest, "exact")?;
            tactic_exact(proof, theory, goal, pretty)
        }
        TacticExpr::Assumption => {
            ensure_no_more_tactics(rest, "assumption")?;
            tactic_assumption(goal, pretty)
        }
        TacticExpr::Have {
            assumption,
            prop,
            proof,
            body,
        } => {
            let rest = explicit_body_or_rest(body.as_ref(), rest, "have")?;
            tactic_have(*assumption, prop, proof, rest, theory, goal, pretty)
        }
        TacticExpr::Eval { limit } => {
            ensure_no_more_tactics(rest, "eval")?;
            tactic_eval(*limit, theory, goal, pretty)
        }
        TacticExpr::Simp { rules } => {
            ensure_no_more_tactics(rest, "simp")?;
            tactic_simp(rules, theory, goal, pretty)
        }
        TacticExpr::Simpa { rules, proof } => {
            ensure_no_more_tactics(rest, "simpa")?;
            tactic_simpa(rules, proof.as_deref(), theory, goal, pretty)
        }
        TacticExpr::Fold { definition } => tactic_fold(*definition, rest, theory, goal, pretty),
        TacticExpr::Apply { theorem, arguments } => {
            ensure_no_more_tactics(rest, "apply")?;
            tactic_apply(*theorem, arguments, theory, goal, pretty)
        }
        TacticExpr::Specialize {
            assumption,
            proof,
            arguments,
            body,
        } => {
            let rest = explicit_body_or_rest(body.as_ref(), rest, "specialize")?;
            tactic_specialize(*assumption, proof, arguments, rest, theory, goal, pretty)
        }
        TacticExpr::Split { left, right } => {
            ensure_no_more_tactics(rest, "split")?;
            tactic_split(left, right, theory, goal, pretty)
        }
        TacticExpr::Exists { witness, proof } => {
            ensure_no_more_tactics(rest, "exists")?;
            tactic_exists(witness, proof, theory, goal, pretty)
        }
        TacticExpr::Obtain {
            existential,
            witness,
            assumption,
            body,
        } => {
            let rest = explicit_body_or_rest(body.as_ref(), rest, "obtain")?;
            tactic_obtain(
                existential,
                *witness,
                *assumption,
                rest,
                theory,
                goal,
                pretty,
            )
        }
        TacticExpr::Cases {
            conjunction,
            left_assumption,
            right_assumption,
            body,
        } => {
            let rest = explicit_body_or_rest(body.as_ref(), rest, "cases")?;
            tactic_cases(
                conjunction,
                *left_assumption,
                *right_assumption,
                rest,
                theory,
                goal,
                pretty,
            )
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
                pretty,
            )
        }
        TacticExpr::Left(proof) => {
            ensure_no_more_tactics(rest, "left")?;
            tactic_left(proof, theory, goal, pretty)
        }
        TacticExpr::Right(proof) => {
            ensure_no_more_tactics(rest, "right")?;
            tactic_right(proof, theory, goal, pretty)
        }
        TacticExpr::Rewrite { equality } => tactic_rewrite(equality, rest, theory, goal, pretty),
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
                pretty,
            )
        }
        TacticExpr::ValueInduction {
            variable,
            symbol_assumption,
            symbol_case,
            lambda_assumption,
            lambda_case,
            nil_case,
            head,
            tail,
            head_induction_hypothesis_assumption,
            tail_induction_hypothesis_assumption,
            cons_case,
        } => {
            ensure_no_more_tactics(rest, "value-induction")?;
            tactic_value_induction(
                *variable,
                *symbol_assumption,
                symbol_case,
                *lambda_assumption,
                lambda_case,
                nil_case,
                *head,
                *tail,
                *head_induction_hypothesis_assumption,
                *tail_induction_hypothesis_assumption,
                cons_case,
                theory,
                goal,
                pretty,
            )
        }
        TacticExpr::Calc { start, steps } => {
            ensure_no_more_tactics(rest, "calc")?;
            tactic_calc(start, steps, theory, goal, pretty)
        }
    };

    result.map_err(|error| add_goal_context(error, tactic, &goal.target, pretty))
}

fn tactic_intro(
    symbol: Symbol,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
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
                        proof: Box::new(tactic_steps_to_proof(rest, theory, &next_goal, pretty)?),
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
                    pretty,
                )?),
            })
        }
        Prop::ForAll { variable, .. } => Err(tactic_failed(
            "intro",
            format!(
                "expected theorem binder {}, got {}\n\
                 reason: intro_binder_mismatch\n\
                 expected_symbol.debug: {:?}\n\
                 actual_symbol.debug: {:?}\n\
                 {}\n\
                 {}",
                symbol_source(*variable, pretty),
                symbol_source(symbol, pretty),
                variable,
                symbol,
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
            ),
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
                proof: Box::new(tactic_steps_to_proof(rest, theory, &next_goal, pretty)?),
            })
        }
        _ => Err(tactic_failed(
            "intro",
            format!(
                "goal is not a forall or implication\n\
                 reason: intro_goal_not_binder\n\
                 {}\n\
                 {}",
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
            ),
        )),
    }
}

fn tactic_exact(
    proof_expr: &ProofExpr,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let proof = proof_expr_to_proof_in_context_with_target(
        proof_expr,
        theory,
        &goal.context,
        Some(&goal.target),
        pretty,
    )?;
    let Some(proven) = theory.proven_prop_in_context(&proof, &goal.context) else {
        return Err(tactic_failed(
            "exact",
            format!(
                "proof expression proves no proposition\n\
                 reason: exact_proof_proves_no_proposition\n\
                 proof_expr.debug: {}\n\
                 {}\n\
                 {}",
                compact_debug(proof_expr),
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
            ),
        ));
    };

    if alpha_eq_prop(&proven, &goal.target) {
        Ok(proof)
    } else {
        Err(tactic_failed(
            "exact",
            exact_mismatch_message(proof_expr, &proven, goal, pretty),
        ))
    }
}

fn exact_mismatch_message(
    proof_expr: &ProofExpr,
    proven: &Prop,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> String {
    format!(
        "proof proves {}, but goal is {}\n\
         reason: exact_mismatch\n\
         proof_expr.debug: {}\n\
         {}\n\
         {}\n\
         {}",
        compact_prop_source(proven, pretty),
        compact_prop_source(&goal.target, pretty),
        compact_debug(proof_expr),
        prop_diagnostic("proof", proven, pretty),
        prop_diagnostic("goal", &goal.target, pretty),
        context_diagnostic("context.locals", &goal.context, pretty)
    )
}

pub(super) fn goal_not_equality_message(
    reason: &'static str,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> String {
    format!(
        "goal is not an equality\n\
         reason: {reason}\n\
         {}\n\
         {}",
        prop_diagnostic("goal", &goal.target, pretty),
        context_diagnostic("context.locals", &goal.context, pretty)
    )
}

fn goal_shape_message(
    reason: &'static str,
    expected: &str,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> String {
    format!(
        "goal is not {expected}\n\
         reason: {reason}\n\
         {}\n\
         {}",
        prop_diagnostic("goal", &goal.target, pretty),
        context_diagnostic("context.locals", &goal.context, pretty)
    )
}

fn tactic_assumption(goal: &Goal, pretty: &PrettyEnv) -> Result<Proof, ProofElaborationError> {
    goal.context
        .iter()
        .find_map(|(symbol, prop)| {
            alpha_eq_prop(prop, &goal.target).then_some(Proof::Assume(*symbol))
        })
        .ok_or_else(|| {
            tactic_failed(
                "assumption",
                format!(
                    "no local assumption matches the goal\n\
                     reason: assumption_not_found\n\
                     {}\n\
                     {}",
                    prop_diagnostic("goal", &goal.target, pretty),
                    context_diagnostic("context.locals", &goal.context, pretty)
                ),
            )
        })
}

fn tactic_have(
    assumption: Symbol,
    prop: &Prop,
    proof_script: &ProofScript,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
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
        pretty,
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
            pretty,
        )?),
    };

    Ok(Proof::ImpliesElim {
        implication: Box::new(implication),
        premise: Box::new(premise_proof),
    })
}

fn tactic_eval(
    limit: usize,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Equal(left, right) = &goal.target else {
        return Err(tactic_failed(
            "eval",
            goal_not_equality_message("eval_goal_not_equality", goal, pretty),
        ));
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
    pretty: &PrettyEnv,
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
        pretty,
        Some(theorem),
        Some(arguments),
    )?;

    if alpha_eq_prop(&prop, &goal.target) {
        Ok(proof)
    } else {
        Err(tactic_failed(
            "apply",
            proof_goal_mismatch_message(
                "apply_mismatch",
                Some(theorem),
                Some(arguments),
                &prop,
                &goal.target,
                &goal.context,
                pretty,
            ),
        ))
    }
}

fn tactic_specialize(
    assumption: Symbol,
    proof_expr: &ProofExpr,
    arguments: &[Computation],
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    if goal.context.contains_key(&assumption) {
        return Err(tactic_failed(
            "specialize",
            format!("assumption symbol {:?} is already in scope", assumption),
        ));
    }

    let proof = proof_expr_to_proof_in_context(proof_expr, theory, &goal.context, pretty)?;
    let prop = theory
        .proven_prop_in_context(&proof, &goal.context)
        .ok_or_else(|| tactic_failed("specialize", "proof expression proves no proposition"))?;
    let (specialized_proof, specialized_prop) = apply_arguments_and_available_implications(
        "specialize",
        proof,
        prop,
        arguments,
        theory,
        &goal.context,
        pretty,
    )?;

    let mut context = goal.context.clone();
    context.insert(assumption, specialized_prop.clone());
    let implication = Proof::ImpliesIntro {
        assumption,
        premise: specialized_prop,
        proof: Box::new(tactic_steps_to_proof(
            rest,
            theory,
            &Goal {
                context,
                target: goal.target.clone(),
            },
            pretty,
        )?),
    };

    Ok(Proof::ImpliesElim {
        implication: Box::new(implication),
        premise: Box::new(specialized_proof),
    })
}

pub(super) fn apply_arguments_and_implications(
    tactic: &'static str,
    mut proof: Proof,
    mut prop: Prop,
    arguments: &[Computation],
    theory: &Theory,
    context: &ProofContext,
    target: Option<&Prop>,
    pretty: &PrettyEnv,
    mismatch_theorem: Option<Name>,
    mismatch_arguments: Option<&[Computation]>,
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
                    proof =
                        apply_available_premise(tactic, proof, premise.as_ref(), context, pretty)?;
                    prop = theory
                        .proven_prop_in_context(&proof, context)
                        .ok_or_else(|| {
                            tactic_failed(tactic, "applying premise produced no proposition")
                        })?;
                    if alpha_eq_prop(&prop, conclusion.as_ref()) {
                        prop = conclusion.as_ref().clone();
                    }
                }
                other => {
                    return Err(tactic_failed(
                        tactic,
                        explicit_argument_error_message(&other, argument, context, pretty),
                    ));
                }
            }
        }
    }

    finish_implications(
        tactic,
        proof,
        prop,
        theory,
        context,
        target,
        pretty,
        mismatch_theorem,
        mismatch_arguments,
    )
}

fn apply_arguments_and_available_implications(
    tactic: &'static str,
    proof: Proof,
    prop: Prop,
    arguments: &[Computation],
    theory: &Theory,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> Result<(Proof, Prop), ProofElaborationError> {
    let (proof, prop) = apply_arguments_and_implications(
        tactic, proof, prop, arguments, theory, context, None, pretty, None, None,
    )?;
    finish_available_implications(tactic, proof, prop, theory, context, pretty)
}

pub(super) fn finish_available_implications(
    tactic: &'static str,
    mut proof: Proof,
    mut prop: Prop,
    theory: &Theory,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> Result<(Proof, Prop), ProofElaborationError> {
    loop {
        let (premise, conclusion) = match &prop {
            Prop::Implies(premise, conclusion) => {
                (premise.as_ref().clone(), conclusion.as_ref().clone())
            }
            _ => {
                return Ok((proof, prop));
            }
        };

        let Ok(next_proof) =
            apply_available_premise(tactic, proof.clone(), &premise, context, pretty)
        else {
            return Ok((proof, prop));
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

fn finish_implications(
    tactic: &'static str,
    mut proof: Proof,
    mut prop: Prop,
    theory: &Theory,
    context: &ProofContext,
    target: Option<&Prop>,
    pretty: &PrettyEnv,
    mismatch_theorem: Option<Name>,
    mismatch_arguments: Option<&[Computation]>,
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
                        proof_goal_mismatch_message(
                            "proof_goal_mismatch",
                            mismatch_theorem,
                            mismatch_arguments,
                            &prop,
                            target,
                            context,
                            pretty,
                        ),
                    )),
                    None => Ok((proof, prop)),
                };
            }
        };

        let next_proof = match target {
            Some(_) => apply_available_premise(tactic, proof.clone(), &premise, context, pretty),
            None => apply_structural_premise(tactic, proof.clone(), &premise, context, pretty),
        };
        let Ok(next_proof) = next_proof else {
            return match target {
                Some(_) => Err(tactic_failed(
                    tactic,
                    unavailable_premise_message(&premise, context, pretty),
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

fn explicit_argument_error_message(
    prop: &Prop,
    argument: &Computation,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> String {
    let argument_is_local_fact =
        matches!(argument, Computation::Var(symbol) if context.contains_key(symbol));
    let local_fact = match argument {
        Computation::Var(symbol) => context.get(symbol).map(|prop| {
            format!(
                "\nargument.local_fact.symbol: {}\nargument.local_fact.prop.source: {}\nargument.local_fact.prop.debug: {}",
                symbol_source(*symbol, pretty),
                compact_prop_source(prop, pretty),
                compact_debug(prop)
            )
        }),
        _ => None,
    }
    .unwrap_or_default();
    let local_fact_hint = if argument_is_local_fact {
        "\nif this local fact is an implication premise, do not pass it as an explicit argument; premises are applied automatically when available"
    } else {
        ""
    };

    match prop {
        Prop::Implies(premise, _) => format!(
            concat!(
                "too many explicit computation arguments; the proof is waiting for an ",
                "implication premise, not another forall argument\n",
                "reason: explicit_argument_hit_implication\n",
                "next explicit argument: {argument_source}{local_fact}\n",
                "argument.source: {argument_source}\n",
                "argument.debug: {argument_debug}\n",
                "remaining premise: {premise_source}\n",
                "remaining_premise.source: {premise_source}\n",
                "remaining_premise.debug: {premise_debug}\n",
                "{context}\n",
                "explicit proof-application arguments instantiate forall-bound computations only; ",
                "implication premises are taken from local assumptions and applied automatically ",
                "when available. Put the premise in scope with `intro`/`have`, then use `exact` ",
                "or `specialize` without passing that proof as an argument"
            ),
            argument_source = compact_computation_source(argument, pretty),
            argument_debug = compact_debug(argument),
            local_fact = local_fact,
            premise_source = compact_prop_source(premise, pretty),
            premise_debug = compact_debug(premise),
            context = context_diagnostic("context.locals", context, pretty)
        ),
        _ => format!(
            concat!(
                "too many explicit computation arguments; proof has no remaining forall binder ",
                "for argument {argument_source}{local_fact}\n",
                "reason: explicit_argument_without_forall\n",
                "argument.source: {argument_source}\n",
                "argument.debug: {argument_debug}\n",
                "current proposition: {prop_source}\n",
                "current_proposition.source: {prop_source}\n",
                "current_proposition.debug: {prop_debug}\n",
                "{context}\n",
                "explicit proof-application arguments instantiate forall-bound computations only",
                "{local_fact_hint}"
            ),
            argument_source = compact_computation_source(argument, pretty),
            argument_debug = compact_debug(argument),
            local_fact = local_fact,
            prop_source = compact_prop_source(prop, pretty),
            prop_debug = compact_debug(prop),
            context = context_diagnostic("context.locals", context, pretty),
            local_fact_hint = local_fact_hint
        ),
    }
}

fn apply_available_premise(
    tactic: &'static str,
    implication: Proof,
    premise: &Prop,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let premise_proof = available_prop_proof(premise, context, pretty).map_err(|_| {
        tactic_failed(
            tactic,
            unavailable_premise_message(premise, context, pretty),
        )
    })?;

    Ok(Proof::ImpliesElim {
        implication: Box::new(implication),
        premise: Box::new(premise_proof),
    })
}

pub(super) fn available_prop_proof(
    prop: &Prop,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let goal = Goal {
        context: context.clone(),
        target: prop.clone(),
    };
    tactic_assumption(&goal, pretty).or_else(|_| {
        primitive_prop_holds(prop, context)
            .then_some(Proof::Primitive(prop.clone()))
            .ok_or_else(|| tactic_failed("available", "proposition is not available"))
    })
}

fn unavailable_premise_message(
    premise: &Prop,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> String {
    format!(
        "premise {} is not available; {}\n\
         reason: premise_not_available\n\
         {}\n\
         {}",
        compact_prop_source(premise, pretty),
        local_facts_message(context, pretty),
        prop_diagnostic("premise", premise, pretty),
        context_diagnostic("context.locals", context, pretty)
    )
}

fn local_facts_message(context: &ProofContext, pretty: &PrettyEnv) -> String {
    if context.is_empty() {
        return "no local facts are in scope".to_owned();
    }

    let mut facts = context.iter().collect::<Vec<_>>();
    facts.sort_by_key(|(symbol, _)| symbol.0);
    let facts = facts
        .into_iter()
        .map(|(symbol, prop)| {
            format!(
                "{}: {}",
                symbol_source(*symbol, pretty),
                compact_prop_source(prop, pretty)
            )
        })
        .collect::<Vec<_>>()
        .join("; ");

    format!("local facts in scope: {facts}")
}

fn proof_goal_mismatch_message(
    reason: &'static str,
    theorem: Option<Name>,
    arguments: Option<&[Computation]>,
    proof_prop: &Prop,
    goal: &Prop,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> String {
    let theorem = theorem
        .map(|theorem| format!("\ntheorem: {}", name_source(theorem, pretty)))
        .unwrap_or_default();
    let arguments = arguments
        .map(|arguments| {
            let arguments = arguments
                .iter()
                .map(|argument| compact_computation_source(argument, pretty))
                .collect::<Vec<_>>()
                .join(" ");
            format!("\narguments.source: ({arguments})")
        })
        .unwrap_or_default();

    format!(
        "proof concludes {}, but goal is {}\n\
         reason: {reason}{theorem}{arguments}\n\
         {}\n\
         {}\n\
         {}",
        compact_prop_source(proof_prop, pretty),
        compact_prop_source(goal, pretty),
        prop_diagnostic("proof", proof_prop, pretty),
        prop_diagnostic("goal", goal, pretty),
        context_diagnostic("context.locals", context, pretty)
    )
}

fn proof_shape_message(
    reason: &'static str,
    expected: &str,
    proof: &Proof,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> String {
    let proof_diagnostic = theory
        .proven_prop_in_context(proof, &goal.context)
        .as_ref()
        .map(|prop| prop_diagnostic("proof", prop, pretty))
        .unwrap_or_else(|| "proof: (proves no proposition)".to_owned());

    format!(
        "proof is not {expected}\n\
         reason: {reason}\n\
         {}\n\
         {}\n\
         {}",
        proof_diagnostic,
        prop_diagnostic("goal", &goal.target, pretty),
        context_diagnostic("context.locals", &goal.context, pretty)
    )
}

fn apply_structural_premise(
    tactic: &'static str,
    implication: Proof,
    premise: &Prop,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    if !structural_primitive_prop_holds(premise, context) {
        return Err(tactic_failed(
            tactic,
            format!(
                "premise {} is not structurally available\n\
                 reason: structural_premise_not_available\n\
                 {}\n\
                 {}",
                compact_prop_source(premise, pretty),
                prop_diagnostic("premise", premise, pretty),
                context_diagnostic("context.locals", context, pretty)
            ),
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
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Prop::And(left, right) = &goal.target else {
        return Err(tactic_failed(
            "split",
            goal_shape_message("split_goal_not_conjunction", "a conjunction", goal, pretty),
        ));
    };

    Ok(Proof::AndIntro(
        Box::new(tactic_script_to_proof(
            left_script,
            theory,
            &Goal {
                context: goal.context.clone(),
                target: left.as_ref().clone(),
            },
            pretty,
        )?),
        Box::new(tactic_script_to_proof(
            right_script,
            theory,
            &Goal {
                context: goal.context.clone(),
                target: right.as_ref().clone(),
            },
            pretty,
        )?),
    ))
}

fn tactic_exists(
    witness: &Computation,
    script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Exists { variable, body } = &goal.target else {
        return Err(tactic_failed(
            "exists",
            goal_shape_message(
                "exists_goal_not_existential",
                "an existential",
                goal,
                pretty,
            ),
        ));
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
        pretty,
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
    context: &ProofContext,
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

fn tactic_obtain(
    existential_expr: &ProofExpr,
    witness: Symbol,
    assumption: Symbol,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let existential =
        proof_expr_to_proof_in_context(existential_expr, theory, &goal.context, pretty)?;
    let context = exists_elim_context(
        "obtain",
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
            pretty,
        )?),
    })
}

fn tactic_cases(
    conjunction_expr: &ProofExpr,
    left_assumption: Symbol,
    right_assumption: Symbol,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    if left_assumption == right_assumption {
        return Err(tactic_failed(
            "cases",
            "left and right assumption names must be distinct",
        ));
    }
    if goal.context.contains_key(&left_assumption) {
        return Err(tactic_failed(
            "cases",
            format!(
                "left assumption symbol {:?} is already in scope",
                left_assumption
            ),
        ));
    }
    if goal.context.contains_key(&right_assumption) {
        return Err(tactic_failed(
            "cases",
            format!(
                "right assumption symbol {:?} is already in scope",
                right_assumption
            ),
        ));
    }

    let conjunction =
        proof_expr_to_proof_in_context(conjunction_expr, theory, &goal.context, pretty)?;
    let Some(Prop::And(left, right)) = theory.proven_prop_in_context(&conjunction, &goal.context)
    else {
        return Err(tactic_failed(
            "cases",
            proof_shape_message(
                "cases_proof_not_conjunction",
                "a conjunction",
                &conjunction,
                theory,
                goal,
                pretty,
            ),
        ));
    };

    let left = left.as_ref().clone();
    let right = right.as_ref().clone();
    let mut context = goal.context.clone();
    context.insert(left_assumption, left.clone());
    context.insert(right_assumption, right.clone());

    let scoped_proof = tactic_steps_to_proof(
        rest,
        theory,
        &Goal {
            context,
            target: goal.target.clone(),
        },
        pretty,
    )?;
    let implication = Proof::ImpliesIntro {
        assumption: left_assumption,
        premise: left,
        proof: Box::new(Proof::ImpliesIntro {
            assumption: right_assumption,
            premise: right,
            proof: Box::new(scoped_proof),
        }),
    };
    let with_left = Proof::ImpliesElim {
        implication: Box::new(implication),
        premise: Box::new(Proof::AndElimLeft(Box::new(conjunction.clone()))),
    };

    Ok(Proof::ImpliesElim {
        implication: Box::new(with_left),
        premise: Box::new(Proof::AndElimRight(Box::new(conjunction))),
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
    pretty: &PrettyEnv,
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

    let disjunction =
        proof_expr_to_proof_in_context(disjunction_expr, theory, &goal.context, pretty)?;
    let Some(Prop::Or(left, right)) = theory.proven_prop_in_context(&disjunction, &goal.context)
    else {
        return Err(tactic_failed(
            "or-elim",
            proof_shape_message(
                "or_elim_proof_not_disjunction",
                "a disjunction",
                &disjunction,
                theory,
                goal,
                pretty,
            ),
        ));
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
            pretty,
        )?),
        right_assumption,
        right_proof: Box::new(tactic_script_to_proof(
            right_script,
            theory,
            &Goal {
                context: right_context,
                target: goal.target.clone(),
            },
            pretty,
        )?),
    })
}

fn tactic_left(
    script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Or(left, right) = &goal.target else {
        return Err(tactic_failed(
            "left",
            goal_shape_message("left_goal_not_disjunction", "a disjunction", goal, pretty),
        ));
    };

    Ok(Proof::OrIntroLeft {
        proof: Box::new(tactic_script_to_proof(
            script,
            theory,
            &Goal {
                context: goal.context.clone(),
                target: left.as_ref().clone(),
            },
            pretty,
        )?),
        right: right.as_ref().clone(),
    })
}

fn tactic_right(
    script: &TacticScript,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Or(left, right) = &goal.target else {
        return Err(tactic_failed(
            "right",
            goal_shape_message("right_goal_not_disjunction", "a disjunction", goal, pretty),
        ));
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
            pretty,
        )?),
    })
}

fn tactic_rewrite(
    equality_expr: &ProofExpr,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let equality = proof_expr_to_proof_in_context(equality_expr, theory, &goal.context, pretty)?;
    let Some(proven) = theory.proven_prop_in_context(&equality, &goal.context) else {
        return Err(tactic_failed(
            "rewrite",
            rewrite_missing_proven_prop_message(&goal.target, pretty),
        ));
    };
    let Prop::Equal(left, right) = proven else {
        return Err(tactic_failed(
            "rewrite",
            rewrite_non_equality_message(&goal.target, &proven, pretty),
        ));
    };

    let placeholder = fresh_rewrite_symbol(&goal.target, &left, &right);
    let Some(template) = rewrite_template(&goal.target, &left, placeholder) else {
        let reverse_placeholder = fresh_rewrite_symbol(&goal.target, &right, &left);
        let right_occurs = rewrite_template(&goal.target, &right, reverse_placeholder).is_some();
        return Err(tactic_failed(
            "rewrite",
            rewrite_missing_left_message(&goal.target, &left, &right, right_occurs, pretty),
        ));
    };

    let rewritten_goal = Goal {
        context: goal.context.clone(),
        target: substitute_prop(&template, placeholder, &right),
    };
    let proof = tactic_steps_to_proof(rest, theory, &rewritten_goal, pretty)?;

    Ok(Proof::Rewrite {
        equality: Box::new(Proof::Symm(Box::new(equality))),
        proof: Box::new(proof),
        variable: placeholder,
        template,
    })
}

fn rewrite_missing_proven_prop_message(goal: &Prop, pretty: &PrettyEnv) -> String {
    format!(
        "rewrite proof proves no proposition\n\
         reason: rewrite_proof_proves_no_proposition\n\
         {}",
        prop_diagnostic("goal", goal, pretty)
    )
}

fn rewrite_non_equality_message(goal: &Prop, proven: &Prop, pretty: &PrettyEnv) -> String {
    format!(
        "rewrite proof is not an equality\n\
         reason: rewrite_proof_not_equality\n\
         current goal: {}\n\
         proof produced: {}\n\
         {}\n\
         {}\n\
         expected: an equality whose left side occurs in the current goal",
        compact_prop_source(goal, pretty),
        compact_prop_source(proven, pretty),
        prop_diagnostic("goal", goal, pretty),
        prop_diagnostic("proof", proven, pretty)
    )
}

fn rewrite_missing_left_message(
    goal: &Prop,
    left: &Computation,
    right: &Computation,
    right_occurs: bool,
    pretty: &PrettyEnv,
) -> String {
    let hint = if right_occurs {
        "\nhint: the right side appears in the goal; try `(rewrite (symm ...))` to rewrite in the reverse direction"
    } else {
        "\nhint: `rewrite` rewrites the first occurrence of the equality's left side"
    };

    format!(
        "goal does not contain the rewrite left side\n\
         reason: rewrite_left_side_missing\n\
         current goal: {}\n\
         equality left side searched for: {}\n\
         equality right side: {}\n\
         {}\n\
         {}\n\
         {}{}",
        compact_prop_source(goal, pretty),
        compact_computation_source(left, pretty),
        compact_computation_source(right, pretty),
        prop_diagnostic("goal", goal, pretty),
        computation_diagnostic("rewrite.lhs", left, pretty),
        computation_diagnostic("rewrite.rhs", right, pretty),
        hint
    )
}

fn tactic_fold(
    definition: Name,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let body = theory
        .computation(definition)
        .cloned()
        .ok_or_else(|| tactic_failed("fold", format!("unknown definition {definition:?}")))?;
    let folded = Computation::Ref(definition);
    let placeholder = fresh_rewrite_symbol(&goal.target, &body, &folded);
    let Some(template) = rewrite_template(&goal.target, &body, placeholder) else {
        return Err(tactic_failed(
            "fold",
            format!(
                "goal does not contain the definition body {}\n\
                 reason: fold_definition_body_missing\n\
                 definition: {}\n\
                 {}\n\
                 {}\n\
                 folded.source: {}\n\
                 folded.debug: {}",
                compact_computation_source(&body, pretty),
                name_source(definition, pretty),
                prop_diagnostic("goal", &goal.target, pretty),
                computation_diagnostic("definition.body", &body, pretty),
                compact_computation_source(&folded, pretty),
                compact_debug(&folded)
            ),
        ));
    };

    let folded_goal = Goal {
        context: goal.context.clone(),
        target: substitute_prop(&template, placeholder, &folded),
    };
    let proof = tactic_steps_to_proof(rest, theory, &folded_goal, pretty)?;

    Ok(Proof::Rewrite {
        equality: Box::new(Proof::Step(folded)),
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
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let (goal_variable, predicate, property) = list_induction_goal(goal, pretty)?;

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
            format!(
                "forall predicate is not an is-list predicate\n\
                 reason: list_induction_predicate_mismatch\n\
                 {}\n\
                 {}\n\
                 {}",
                prop_diagnostic("predicate", &predicate, pretty),
                prop_diagnostic("expected", &expected_predicate, pretty),
                prop_diagnostic("goal", &goal.target, pretty)
            ),
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
        base: Box::new(tactic_script_to_proof(base, theory, &base_goal, pretty)?),
        head,
        tail,
        induction_hypothesis_assumption,
        step: Box::new(tactic_script_to_proof(step, theory, &step_goal, pretty)?),
    })
}

#[allow(clippy::too_many_arguments)]
fn tactic_value_induction(
    variable: Symbol,
    symbol_assumption: Symbol,
    symbol_case: &TacticScript,
    lambda_assumption: Symbol,
    lambda_case: &TacticScript,
    nil_case: &TacticScript,
    head: Symbol,
    tail: Symbol,
    head_induction_hypothesis_assumption: Symbol,
    tail_induction_hypothesis_assumption: Symbol,
    cons_case: &TacticScript,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let (goal_variable, predicate, property) = value_induction_goal(goal, pretty)?;

    if variable != goal_variable {
        return Err(tactic_failed(
            "value-induction",
            format!(
                "expected theorem binder {:?}, got {:?}",
                goal_variable, variable
            ),
        ));
    }

    let expected_predicate = is_value(Computation::Var(variable));
    if !alpha_eq_prop(&predicate, &expected_predicate) {
        return Err(tactic_failed(
            "value-induction",
            format!(
                "forall predicate is not an is-value predicate\n\
                 reason: value_induction_predicate_mismatch\n\
                 {}\n\
                 {}\n\
                 {}",
                prop_diagnostic("predicate", &predicate, pretty),
                prop_diagnostic("expected", &expected_predicate, pretty),
                prop_diagnostic("goal", &goal.target, pretty)
            ),
        ));
    }

    let variable_computation = Computation::Var(variable);
    let variable_target = substitute_prop(&property, variable, &variable_computation);

    let mut symbol_context = goal.context.clone();
    symbol_context.insert(variable, is_value(variable_computation.clone()));
    symbol_context.insert(
        symbol_assumption,
        value_kind_is_kind(variable_computation.clone(), SYMBOL_KIND_SYMBOL),
    );
    let symbol_goal = Goal {
        context: symbol_context,
        target: variable_target.clone(),
    };

    let mut lambda_context = goal.context.clone();
    lambda_context.insert(variable, is_value(variable_computation));
    lambda_context.insert(
        lambda_assumption,
        value_kind_is_kind(Computation::Var(variable), LAMBDA_KIND_SYMBOL),
    );
    let lambda_goal = Goal {
        context: lambda_context,
        target: variable_target,
    };

    let nil_goal = Goal {
        context: goal.context.clone(),
        target: substitute_prop(&property, variable, &Computation::Nil),
    };

    let head_var = Computation::Var(head);
    let tail_var = Computation::Var(tail);
    let cons = Computation::Cons {
        head: Box::new(head_var.clone()),
        tail: Box::new(tail_var.clone()),
    };
    let mut cons_context = goal.context.clone();
    cons_context.insert(head, is_value(head_var.clone()));
    cons_context.insert(tail, is_list(tail_var.clone()));
    cons_context.insert(
        head_induction_hypothesis_assumption,
        substitute_prop(&property, variable, &head_var),
    );
    cons_context.insert(
        tail_induction_hypothesis_assumption,
        substitute_prop(&property, variable, &tail_var),
    );
    let cons_goal = Goal {
        context: cons_context,
        target: substitute_prop(&property, variable, &cons),
    };

    Ok(Proof::ValueInduction {
        variable,
        property,
        symbol_assumption,
        symbol_case: Box::new(tactic_script_to_proof(
            symbol_case,
            theory,
            &symbol_goal,
            pretty,
        )?),
        lambda_assumption,
        lambda_case: Box::new(tactic_script_to_proof(
            lambda_case,
            theory,
            &lambda_goal,
            pretty,
        )?),
        nil_case: Box::new(tactic_script_to_proof(nil_case, theory, &nil_goal, pretty)?),
        head,
        tail,
        head_induction_hypothesis_assumption,
        tail_induction_hypothesis_assumption,
        cons_case: Box::new(tactic_script_to_proof(
            cons_case, theory, &cons_goal, pretty,
        )?),
    })
}

fn list_induction_goal(
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<(Symbol, Prop, Prop), ProofElaborationError> {
    let target = &goal.target;
    let Prop::ForAll { variable, body } = target else {
        return Err(tactic_failed(
            "list-induction",
            goal_shape_message("list_induction_goal_not_forall", "a forall", goal, pretty),
        ));
    };

    let Prop::Implies(predicate, body) = body.as_ref() else {
        return Err(tactic_failed(
            "list-induction",
            format!(
                "forall body is not a predicate implication\n\
                 reason: list_induction_body_not_implication\n\
                 {}\n\
                 {}",
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
            ),
        ));
    };

    Ok((*variable, predicate.as_ref().clone(), body.as_ref().clone()))
}

fn value_induction_goal(
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<(Symbol, Prop, Prop), ProofElaborationError> {
    let target = &goal.target;
    let Prop::ForAll { variable, body } = target else {
        return Err(tactic_failed(
            "value-induction",
            goal_shape_message("value_induction_goal_not_forall", "a forall", goal, pretty),
        ));
    };

    let Prop::Implies(predicate, body) = body.as_ref() else {
        return Err(tactic_failed(
            "value-induction",
            format!(
                "forall body is not a predicate implication\n\
                 reason: value_induction_body_not_implication\n\
                 {}\n\
                 {}",
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
            ),
        ));
    };

    Ok((*variable, predicate.as_ref().clone(), body.as_ref().clone()))
}

fn value_kind_is_kind(computation: Computation, kind: Symbol) -> Prop {
    equal(
        symbol_eq(value_kind(computation), Computation::Quote(kind)),
        Computation::Quote(TRUE_SYMBOL),
    )
}

fn tactic_calc(
    start: &Computation,
    steps: &[CalcStep],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Equal(goal_left, goal_right) = &goal.target else {
        return Err(tactic_failed(
            "calc",
            goal_not_equality_message("calc_goal_not_equality", goal, pretty),
        ));
    };

    if !alpha_eq_computation(start, goal_left) {
        return Err(tactic_failed(
            "calc",
            format!(
                "calc starts at {}, but goal starts at {}\n\
                 reason: calc_start_mismatch\n\
                 {}\n\
                 {}\n\
                 {}\n\
                 {}",
                compact_computation_source(start, pretty),
                compact_computation_source(goal_left, pretty),
                computation_diagnostic("calc.start", start, pretty),
                computation_diagnostic("goal.left", goal_left, pretty),
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
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
            pretty,
        )?);
        previous = step.target.clone();
    }

    if !alpha_eq_computation(&previous, goal_right) {
        return Err(tactic_failed(
            "calc",
            format!(
                "calc ends at {}, but goal ends at {}\n\
                 reason: calc_end_mismatch\n\
                 {}\n\
                 {}\n\
                 {}\n\
                 {}",
                compact_computation_source(&previous, pretty),
                compact_computation_source(goal_right, pretty),
                computation_diagnostic("calc.end", &previous, pretty),
                computation_diagnostic("goal.right", goal_right, pretty),
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
            ),
        ));
    }

    trans_chain(proofs).ok_or_else(|| {
        tactic_failed(
            "calc",
            format!(
                "calc has no steps\n\
                 reason: calc_empty\n\
                 {}\n\
                 {}",
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
            ),
        )
    })
}

fn proof_script_to_proof_for_goal(
    script: &ProofScript,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    match script {
        ProofScript::Proof(proof) => tactic_exact(proof, theory, goal, pretty),
        ProofScript::By(script) => tactic_script_to_proof(script, theory, goal, pretty),
    }
}

pub(super) fn trans_chain(proofs: Vec<Proof>) -> Option<Proof> {
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

fn add_goal_context(
    error: ProofElaborationError,
    tactic_expr: &TacticExpr,
    target: &Prop,
    pretty: &PrettyEnv,
) -> ProofElaborationError {
    match error {
        ProofElaborationError::TacticFailed { tactic, message } => {
            ProofElaborationError::TacticFailed {
                tactic,
                message: format!(
                    "{message}\n\
                     context.tactic_expr.debug: {}\n\
                     context.goal.source: {}\n\
                     context.goal.debug: {}",
                    compact_debug(tactic_expr),
                    compact_prop_source(target, pretty),
                    compact_debug(target)
                ),
            }
        }
        ProofElaborationError::InSubproof { form, error } => ProofElaborationError::InSubproof {
            form,
            error: Box::new(add_goal_context(*error, tactic_expr, target, pretty)),
        },
        error => error,
    }
}

pub(super) fn fresh_rewrite_symbol(
    target: &Prop,
    left: &Computation,
    right: &Computation,
) -> Symbol {
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
        Prop::Absurd => None,
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
        Prop::Absurd => {}
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
