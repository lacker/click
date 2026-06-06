//! Tactic-script elaboration into kernel proofs.

use std::collections::{HashMap, HashSet};

use crate::kernel::{primitive_prop_holds, structural_primitive_prop_holds};
use crate::{
    Computation, Context, LAMBDA_KIND_SYMBOL, Lambda, ListCase, Name, Proof, Prop,
    SYMBOL_KIND_SYMBOL, Symbol, TRUE_SYMBOL, Theory, alpha_eq_computation, alpha_eq_prop, equal,
    free_symbols, is_list, is_value, substitute_prop, symbol_eq, value_kind,
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

    let result = match tactic {
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
        TacticExpr::Simp { rules } => {
            ensure_no_more_tactics(rest, "simp")?;
            tactic_simp(rules, theory, goal)
        }
        TacticExpr::Simpa { rules, proof } => {
            ensure_no_more_tactics(rest, "simpa")?;
            tactic_simpa(rules, proof.as_deref(), theory, goal)
        }
        TacticExpr::Fold { definition } => tactic_fold(*definition, rest, theory, goal),
        TacticExpr::Apply { theorem, arguments } => {
            ensure_no_more_tactics(rest, "apply")?;
            tactic_apply(*theorem, arguments, theory, goal)
        }
        TacticExpr::Specialize {
            assumption,
            proof,
            arguments,
            body,
        } => {
            let rest = explicit_body_or_rest(body.as_ref(), rest, "specialize")?;
            tactic_specialize(*assumption, proof, arguments, rest, theory, goal)
        }
        TacticExpr::Split { left, right } => {
            ensure_no_more_tactics(rest, "split")?;
            tactic_split(left, right, theory, goal)
        }
        TacticExpr::Exists { witness, proof } => {
            ensure_no_more_tactics(rest, "exists")?;
            tactic_exists(witness, proof, theory, goal)
        }
        TacticExpr::Obtain {
            existential,
            witness,
            assumption,
            body,
        } => {
            let rest = explicit_body_or_rest(body.as_ref(), rest, "obtain")?;
            tactic_obtain(existential, *witness, *assumption, rest, theory, goal)
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
            )
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
            )
        }
        TacticExpr::Calc { start, steps } => {
            ensure_no_more_tactics(rest, "calc")?;
            tactic_calc(start, steps, theory, goal)
        }
    };

    result.map_err(|error| add_goal_context(error, tactic, &goal.target))
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

const SIMP_STEP_LIMIT: usize = 128;
const SIMP_TRACE_LIMIT: usize = 32;
const SIMP_TRACE_VALUE_LIMIT: usize = 240;

fn tactic_simp(
    rules: &[ProofExpr],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Equal(left, right) = &goal.target else {
        return Err(tactic_failed("simp", "goal is not an equality"));
    };

    let goal_result = simplify_equality("simp", left, right, rules, theory, &goal.context)?;

    if !alpha_eq_computation(&goal_result.left.result, &goal_result.right.result) {
        return Err(tactic_failed(
            "simp",
            simp_failure_message(left, &goal_result.left, right, &goal_result.right),
        ));
    }

    Ok(goal_equality_proof_from_simplified(goal_result))
}

fn tactic_simpa(
    rules: &[ProofExpr],
    proof_expr: Option<&ProofExpr>,
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Equal(goal_left, goal_right) = &goal.target else {
        return Err(tactic_failed("simpa", "goal is not an equality"));
    };

    let goal_result =
        simplify_equality("simpa", goal_left, goal_right, rules, theory, &goal.context)?;
    let Some(proof_expr) = proof_expr else {
        if !alpha_eq_computation(&goal_result.left.result, &goal_result.right.result) {
            return Err(tactic_failed(
                "simpa",
                simp_failure_message(goal_left, &goal_result.left, goal_right, &goal_result.right),
            ));
        }
        return Ok(goal_equality_proof_from_simplified(goal_result));
    };

    let proof = proof_expr_to_proof_in_context(proof_expr, theory, &goal.context)?;
    let prop = theory
        .proven_prop_in_context(&proof, &goal.context)
        .ok_or_else(|| tactic_failed("simpa", "using proof proves no proposition"))?;
    let (proof, prop) = finish_available_implications("simpa", proof, prop, theory, &goal.context)?;
    let Prop::Equal(proof_left, proof_right) = prop else {
        return Err(tactic_failed(
            "simpa",
            format!("using proof proves {:?}, not an equality", prop),
        ));
    };
    let proof_result = simplify_equality(
        "simpa",
        &proof_left,
        &proof_right,
        rules,
        theory,
        &goal.context,
    )?;

    if alpha_eq_computation(&goal_result.left.result, &proof_result.left.result)
        && alpha_eq_computation(&goal_result.right.result, &proof_result.right.result)
    {
        return Ok(simpa_using_proof(goal_result, proof_result, proof));
    }

    Err(tactic_failed(
        "simpa",
        simpa_failure_message(
            goal_left,
            &goal_result.left,
            goal_right,
            &goal_result.right,
            &proof_left,
            &proof_result.left,
            &proof_right,
            &proof_result.right,
        ),
    ))
}

struct SimpResult {
    result: Computation,
    proof: Proof,
    trace: SimpTrace,
}

#[derive(Default)]
struct SimpTrace {
    steps: Vec<String>,
    omitted_steps: usize,
}

impl SimpTrace {
    fn push(&mut self, step: impl Into<String>) {
        if self.steps.len() < SIMP_TRACE_LIMIT {
            self.steps.push(step.into());
        } else {
            self.omitted_steps += 1;
        }
    }

    fn push_change(&mut self, label: impl Into<String>, before: &Computation, after: &Computation) {
        self.push(format!(
            "{}: {} -> {}",
            label.into(),
            compact_debug(before),
            compact_debug(after)
        ));
    }

    fn extend(&mut self, other: SimpTrace) {
        for step in other.steps {
            self.push(step);
        }
        self.omitted_steps += other.omitted_steps;
    }

    fn total_steps(&self) -> usize {
        self.steps.len() + self.omitted_steps
    }
}

struct SimpEqualityResult {
    left: SimpResult,
    right: SimpResult,
}

fn simplify_equality(
    tactic: &'static str,
    left: &Computation,
    right: &Computation,
    rules: &[ProofExpr],
    theory: &Theory,
    context: &Context,
) -> Result<SimpEqualityResult, ProofElaborationError> {
    Ok(SimpEqualityResult {
        left: simplify_computation(tactic, left.clone(), rules, theory, context)?,
        right: simplify_computation(tactic, right.clone(), rules, theory, context)?,
    })
}

fn goal_equality_proof_from_simplified(result: SimpEqualityResult) -> Proof {
    Proof::Trans(
        Box::new(result.left.proof),
        Box::new(Proof::Symm(Box::new(result.right.proof))),
    )
}

fn simpa_using_proof(
    goal_result: SimpEqualityResult,
    proof_result: SimpEqualityResult,
    proof: Proof,
) -> Proof {
    let simplified_proof = Proof::Trans(
        Box::new(Proof::Symm(Box::new(proof_result.left.proof))),
        Box::new(Proof::Trans(
            Box::new(proof),
            Box::new(proof_result.right.proof),
        )),
    );

    Proof::Trans(
        Box::new(goal_result.left.proof),
        Box::new(Proof::Trans(
            Box::new(simplified_proof),
            Box::new(Proof::Symm(Box::new(goal_result.right.proof))),
        )),
    )
}

fn simplify_computation(
    tactic: &'static str,
    original: Computation,
    rules: &[ProofExpr],
    theory: &Theory,
    context: &Context,
) -> Result<SimpResult, ProofElaborationError> {
    let mut current = original.clone();
    let mut proofs = Vec::new();
    let mut trace = SimpTrace::default();
    let mut seen = vec![current.clone()];

    for _ in 0..SIMP_STEP_LIMIT {
        if let Some(rewrite) = simp_rewrite(tactic, &current, rules, theory, context)? {
            trace.extend(rewrite.trace);
            proofs.push(rewrite.proof);
            current = rewrite.result;
            record_simp_state(tactic, &mut seen, &current, &trace)?;
            continue;
        }

        if let Some(rewrite) = simp_child(tactic, &current, rules, theory, context)? {
            trace.extend(rewrite.trace);
            proofs.push(rewrite.proof);
            current = rewrite.result;
            record_simp_state(tactic, &mut seen, &current, &trace)?;
            continue;
        }

        match theory.reduce_in_context(&current, context) {
            crate::Step::Reduced(next) => {
                trace.push_change("kernel reduction", &current, &next);
                proofs.push(Proof::Step(current));
                current = next;
                record_simp_state(tactic, &mut seen, &current, &trace)?;
                continue;
            }
            crate::Step::Normal => {}
        }

        return Ok(SimpResult {
            result: current,
            proof: equality_chain_or_refl(original, proofs),
            trace,
        });
    }

    Err(tactic_failed(
        tactic,
        format!(
            "simplification exceeded {SIMP_STEP_LIMIT} steps\nsteps:\n{}",
            format_simp_trace(&trace)
        ),
    ))
}

struct SimpRewrite {
    result: Computation,
    proof: Proof,
    trace: SimpTrace,
}

fn simp_rewrite(
    tactic: &'static str,
    target: &Computation,
    rules: &[ProofExpr],
    theory: &Theory,
    context: &Context,
) -> Result<Option<SimpRewrite>, ProofElaborationError> {
    for (rule_index, rule) in rules.iter().enumerate() {
        if let Some(rewrite) =
            simp_rewrite_with_rule(tactic, rule_index, rule, target, theory, context)?
        {
            return Ok(Some(rewrite));
        }
    }

    Ok(None)
}

struct SimpRule {
    binders: Vec<Symbol>,
    lhs: Computation,
}

fn simp_rewrite_with_rule(
    tactic: &'static str,
    rule_index: usize,
    rule: &ProofExpr,
    target: &Computation,
    theory: &Theory,
    context: &Context,
) -> Result<Option<SimpRewrite>, ProofElaborationError> {
    let proof = proof_expr_to_proof_in_context(rule, theory, context)?;
    let prop = theory
        .proven_prop_in_context(&proof, context)
        .ok_or_else(|| tactic_failed(tactic, "simp rule proves no proposition"))?;

    let candidates = simp_rule_candidates(proof, prop);
    let mut saw_rewrite_rule = false;

    for (proof, prop) in candidates {
        let Ok(simp_rule) = parse_simp_rule(tactic, rule, &prop) else {
            continue;
        };
        saw_rewrite_rule = true;

        let mut substitutions = HashMap::new();
        let matchable = simp_rule.binders.iter().copied().collect::<HashSet<_>>();
        if !match_simp_pattern(&simp_rule.lhs, target, &matchable, &mut substitutions) {
            continue;
        }

        let Some((proof, proven)) =
            instantiate_simp_rule(tactic, rule, proof, prop, &substitutions, theory, context)?
        else {
            continue;
        };

        match proven {
            Prop::Equal(left, right) => {
                if !alpha_eq_computation(&left, target) {
                    continue;
                }
                if alpha_eq_computation(&right, target) {
                    continue;
                }
                if let crate::Step::Reduced(reduced) = theory.reduce_in_context(&right, context) {
                    if alpha_eq_computation(&reduced, target) {
                        return Err(tactic_failed(
                            tactic,
                            simp_expansion_rule_message(rule_index, rule, target, &right),
                        ));
                    }
                }
                let mut trace = SimpTrace::default();
                trace.push_change(
                    format!(
                        "rewrite with rule {} ({})",
                        rule_index + 1,
                        compact_debug(rule)
                    ),
                    target,
                    &right,
                );
                return Ok(Some(SimpRewrite {
                    result: right,
                    proof,
                    trace,
                }));
            }
            Prop::Implies(_, _) => continue,
            _ => {}
        }
    }

    if saw_rewrite_rule {
        Ok(None)
    } else {
        Err(tactic_failed(
            tactic,
            format!("rule {rule:?} is not an equality rewrite rule"),
        ))
    }
}

fn simp_rule_candidates(proof: Proof, prop: Prop) -> Vec<(Proof, Prop)> {
    match prop {
        Prop::And(left, right) => {
            let left_proof = Proof::AndElimLeft(Box::new(proof.clone()));
            let right_proof = Proof::AndElimRight(Box::new(proof));

            let mut candidates = simp_rule_candidates(left_proof, *left);
            candidates.extend(simp_rule_candidates(right_proof, *right));
            candidates
        }
        _ => vec![(proof, prop)],
    }
}

fn instantiate_simp_rule(
    tactic: &'static str,
    rule: &ProofExpr,
    mut proof: Proof,
    mut prop: Prop,
    substitutions: &HashMap<Symbol, Computation>,
    theory: &Theory,
    context: &Context,
) -> Result<Option<(Proof, Prop)>, ProofElaborationError> {
    loop {
        match prop {
            Prop::ForAll { variable, body } => {
                let Some(argument) = substitutions.get(&variable).cloned() else {
                    return Err(tactic_failed(
                        tactic,
                        format!("could not infer argument {variable:?} for rule {rule:?}"),
                    ));
                };
                let expected = substitute_prop(&body, variable, &argument);
                proof = Proof::ForAllElim {
                    forall: Box::new(proof),
                    argument,
                };
                prop = theory
                    .proven_prop_in_context(&proof, context)
                    .ok_or_else(|| {
                        tactic_failed(tactic, "forall elimination produced no proposition")
                    })?;
                if alpha_eq_prop(&prop, &expected) {
                    prop = expected;
                }
            }
            Prop::Implies(premise, conclusion) => {
                let Ok(premise_proof) = available_prop_proof(&premise, context) else {
                    return Ok(None);
                };
                proof = Proof::ImpliesElim {
                    implication: Box::new(proof),
                    premise: Box::new(premise_proof),
                };
                prop = theory
                    .proven_prop_in_context(&proof, context)
                    .ok_or_else(|| {
                        tactic_failed(tactic, "applying premise produced no proposition")
                    })?;
                if alpha_eq_prop(&prop, &conclusion) {
                    prop = *conclusion;
                }
            }
            _ => return Ok(Some((proof, prop))),
        }
    }
}

fn parse_simp_rule(
    tactic: &'static str,
    rule: &ProofExpr,
    prop: &Prop,
) -> Result<SimpRule, ProofElaborationError> {
    let mut binders = Vec::new();
    let mut prop = prop.clone();

    loop {
        match prop {
            Prop::ForAll { variable, body } => {
                binders.push(variable);
                prop = *body;
            }
            Prop::Implies(_, conclusion) => {
                prop = *conclusion;
            }
            Prop::Equal(left, _right) => {
                return Ok(SimpRule { binders, lhs: left });
            }
            _ => {
                return Err(tactic_failed(
                    tactic,
                    format!("rule {rule:?} is not an equality rewrite rule"),
                ));
            }
        }
    }
}

fn match_simp_pattern(
    pattern: &Computation,
    target: &Computation,
    matchable: &HashSet<Symbol>,
    substitutions: &mut HashMap<Symbol, Computation>,
) -> bool {
    if let Computation::Var(symbol) = pattern {
        if matchable.contains(symbol) {
            return match substitutions.get(symbol) {
                Some(existing) => alpha_eq_computation(existing, target),
                None => {
                    substitutions.insert(*symbol, target.clone());
                    true
                }
            };
        }
    }

    match (pattern, target) {
        (
            Computation::Apply {
                function: pattern_function,
                argument: pattern_argument,
            },
            Computation::Apply {
                function: target_function,
                argument: target_argument,
            },
        ) => {
            match_simp_pattern(pattern_function, target_function, matchable, substitutions)
                && match_simp_pattern(pattern_argument, target_argument, matchable, substitutions)
        }
        (Computation::Lambda(pattern), Computation::Lambda(target)) => {
            match_lambda_pattern(pattern, target, matchable, substitutions)
        }
        (Computation::Nil, Computation::Nil) => true,
        (
            Computation::Cons {
                head: pattern_head,
                tail: pattern_tail,
            },
            Computation::Cons {
                head: target_head,
                tail: target_tail,
            },
        ) => {
            match_simp_pattern(pattern_head, target_head, matchable, substitutions)
                && match_simp_pattern(pattern_tail, target_tail, matchable, substitutions)
        }
        (Computation::Head(pattern), Computation::Head(target))
        | (Computation::Tail(pattern), Computation::Tail(target))
        | (Computation::ValueKind(pattern), Computation::ValueKind(target)) => {
            match_simp_pattern(pattern, target, matchable, substitutions)
        }
        (Computation::ListCase(pattern), Computation::ListCase(target)) => {
            match_list_case_pattern(pattern, target, matchable, substitutions)
        }
        (
            Computation::If {
                condition: pattern_condition,
                then_branch: pattern_then,
                else_branch: pattern_else,
            },
            Computation::If {
                condition: target_condition,
                then_branch: target_then,
                else_branch: target_else,
            },
        ) => {
            match_simp_pattern(
                pattern_condition,
                target_condition,
                matchable,
                substitutions,
            ) && match_simp_pattern(pattern_then, target_then, matchable, substitutions)
                && match_simp_pattern(pattern_else, target_else, matchable, substitutions)
        }
        (
            Computation::SymbolEq {
                left: pattern_left,
                right: pattern_right,
            },
            Computation::SymbolEq {
                left: target_left,
                right: target_right,
            },
        ) => {
            match_simp_pattern(pattern_left, target_left, matchable, substitutions)
                && match_simp_pattern(pattern_right, target_right, matchable, substitutions)
        }
        (Computation::Ref(pattern), Computation::Ref(target)) => pattern == target,
        (Computation::Error(pattern), Computation::Error(target)) => pattern == target,
        (Computation::Diverge, Computation::Diverge) => true,
        (Computation::Var(pattern), Computation::Var(target)) => pattern == target,
        (Computation::Quote(pattern), Computation::Quote(target)) => pattern == target,
        _ => false,
    }
}

fn match_lambda_pattern(
    pattern: &Lambda,
    target: &Lambda,
    matchable: &HashSet<Symbol>,
    substitutions: &mut HashMap<Symbol, Computation>,
) -> bool {
    if pattern.parameter != target.parameter {
        return false;
    }

    let mut matchable = matchable.clone();
    matchable.remove(&pattern.parameter);
    match_simp_pattern(&pattern.body, &target.body, &matchable, substitutions)
}

fn match_list_case_pattern(
    pattern: &ListCase,
    target: &ListCase,
    matchable: &HashSet<Symbol>,
    substitutions: &mut HashMap<Symbol, Computation>,
) -> bool {
    if pattern.cons != target.cons {
        return false;
    }

    let mut cons_case_matchable = matchable.clone();
    cons_case_matchable.remove(&pattern.cons);
    match_simp_pattern(&pattern.list, &target.list, matchable, substitutions)
        && match_simp_pattern(&pattern.nil, &target.nil, matchable, substitutions)
        && match_simp_pattern(
            &pattern.cons_case,
            &target.cons_case,
            &cons_case_matchable,
            substitutions,
        )
}

fn equality_chain_or_refl(original: Computation, proofs: Vec<Proof>) -> Proof {
    trans_chain(proofs).unwrap_or(Proof::Refl(original))
}

fn simp_failure_message(
    left_original: &Computation,
    left_result: &SimpResult,
    right_original: &Computation,
    right_result: &SimpResult,
) -> String {
    format!(
        "simplified goal, but the sides still differ\n\
         left original: {}\n\
         left result: {}\n\
         left steps:\n{}\n\
         right original: {}\n\
         right result: {}\n\
         right steps:\n{}",
        compact_debug(left_original),
        compact_debug(&left_result.result),
        format_simp_trace(&left_result.trace),
        compact_debug(right_original),
        compact_debug(&right_result.result),
        format_simp_trace(&right_result.trace)
    )
}

fn simpa_failure_message(
    goal_left_original: &Computation,
    goal_left_result: &SimpResult,
    goal_right_original: &Computation,
    goal_right_result: &SimpResult,
    proof_left_original: &Computation,
    proof_left_result: &SimpResult,
    proof_right_original: &Computation,
    proof_right_result: &SimpResult,
) -> String {
    format!(
        "simplified goal and using proof, but they do not match\n\
         goal left original: {}\n\
         goal left result: {}\n\
         goal left steps:\n{}\n\
         goal right original: {}\n\
         goal right result: {}\n\
         goal right steps:\n{}\n\
         using left original: {}\n\
         using left result: {}\n\
         using left steps:\n{}\n\
         using right original: {}\n\
         using right result: {}\n\
         using right steps:\n{}",
        compact_debug(goal_left_original),
        compact_debug(&goal_left_result.result),
        format_simp_trace(&goal_left_result.trace),
        compact_debug(goal_right_original),
        compact_debug(&goal_right_result.result),
        format_simp_trace(&goal_right_result.trace),
        compact_debug(proof_left_original),
        compact_debug(&proof_left_result.result),
        format_simp_trace(&proof_left_result.trace),
        compact_debug(proof_right_original),
        compact_debug(&proof_right_result.result),
        format_simp_trace(&proof_right_result.trace)
    )
}

fn format_simp_trace(trace: &SimpTrace) -> String {
    if trace.steps.is_empty() {
        return "  (no simplification steps)".to_string();
    }

    let mut lines = Vec::new();
    for (index, step) in trace.steps.iter().enumerate() {
        lines.push(format!("  {}. {step}", index + 1));
    }
    if trace.omitted_steps > 0 {
        lines.push(format!("  ... {} more steps omitted", trace.omitted_steps));
    }
    lines.join("\n")
}

fn record_simp_state(
    tactic: &'static str,
    seen: &mut Vec<Computation>,
    current: &Computation,
    trace: &SimpTrace,
) -> Result<(), ProofElaborationError> {
    if let Some(first_seen_step) = seen
        .iter()
        .position(|seen| alpha_eq_computation(seen, current))
    {
        return Err(tactic_failed(
            tactic,
            simp_cycle_message(first_seen_step, current, trace),
        ));
    }

    seen.push(current.clone());
    Ok(())
}

fn simp_cycle_message(first_seen_step: usize, repeated: &Computation, trace: &SimpTrace) -> String {
    format!(
        "simplification cycle detected after {} steps\n\
         repeated term first seen after {first_seen_step} steps: {}\n\
         this usually means a simp rule is oriented as an expansion that kernel reduction can undo; \
         use explicit `rewrite`, `eval`, or `fold` for one-shot expansion, or orient simp rules toward canonical forms\n\
         steps:\n{}",
        trace.total_steps(),
        compact_debug(repeated),
        format_simp_trace(trace)
    )
}

fn simp_expansion_rule_message(
    rule_index: usize,
    rule: &ProofExpr,
    target: &Computation,
    expanded: &Computation,
) -> String {
    let fold_hint = match expanded {
        Computation::Ref(_) => " use `(fold <definition>)` for this source-level name,".to_string(),
        _ => " use `fold` for named definitions,".to_string(),
    };

    format!(
        "simp rule {} ({}) is oriented as an expansion\n\
         rewriting {} to {} is immediately undone by kernel reduction;{} \
         or use explicit `rewrite`/`eval` for one-shot expansion; simp rules should move toward canonical forms",
        rule_index + 1,
        compact_debug(rule),
        compact_debug(target),
        compact_debug(expanded),
        fold_hint
    )
}

fn compact_debug(value: &impl std::fmt::Debug) -> String {
    let mut text = format!("{value:?}");
    if text.chars().count() <= SIMP_TRACE_VALUE_LIMIT {
        return text;
    }

    let cutoff = text
        .char_indices()
        .nth(SIMP_TRACE_VALUE_LIMIT)
        .map(|(index, _)| index)
        .unwrap_or(text.len());
    text.truncate(cutoff);
    text.push_str("...");
    text
}

fn simp_child(
    tactic: &'static str,
    computation: &Computation,
    rules: &[ProofExpr],
    theory: &Theory,
    context: &Context,
) -> Result<Option<SimpRewrite>, ProofElaborationError> {
    match computation {
        Computation::Apply { function, argument } => simplify_child(
            tactic,
            computation,
            argument,
            |argument| Computation::Apply {
                function: function.clone(),
                argument: Box::new(argument),
            },
            rules,
            theory,
            context,
        )?
        .map_or_else(
            || {
                simplify_child(
                    tactic,
                    computation,
                    function,
                    |function| Computation::Apply {
                        function: Box::new(function),
                        argument: argument.clone(),
                    },
                    rules,
                    theory,
                    context,
                )
            },
            |rewrite| Ok(Some(rewrite)),
        ),
        Computation::Cons { head, tail } => simplify_child(
            tactic,
            computation,
            head,
            |head| Computation::Cons {
                head: Box::new(head),
                tail: tail.clone(),
            },
            rules,
            theory,
            context,
        )?
        .map_or_else(
            || {
                simplify_child(
                    tactic,
                    computation,
                    tail,
                    |tail| Computation::Cons {
                        head: head.clone(),
                        tail: Box::new(tail),
                    },
                    rules,
                    theory,
                    context,
                )
            },
            |rewrite| Ok(Some(rewrite)),
        ),
        Computation::Head(child) => simplify_child(
            tactic,
            computation,
            child,
            |child| Computation::Head(Box::new(child)),
            rules,
            theory,
            context,
        ),
        Computation::Tail(child) => simplify_child(
            tactic,
            computation,
            child,
            |child| Computation::Tail(Box::new(child)),
            rules,
            theory,
            context,
        ),
        Computation::ListCase(list_case) => simplify_child(
            tactic,
            computation,
            &list_case.list,
            |list| {
                let mut list_case = list_case.clone();
                list_case.list = Box::new(list);
                Computation::ListCase(list_case)
            },
            rules,
            theory,
            context,
        )?
        .map_or_else(
            || {
                simplify_child(
                    tactic,
                    computation,
                    &list_case.nil,
                    |nil| {
                        let mut list_case = list_case.clone();
                        list_case.nil = Box::new(nil);
                        Computation::ListCase(list_case)
                    },
                    rules,
                    theory,
                    context,
                )
            },
            |rewrite| Ok(Some(rewrite)),
        ),
        Computation::If {
            condition,
            then_branch,
            else_branch,
        } => simplify_child(
            tactic,
            computation,
            condition,
            |condition| Computation::If {
                condition: Box::new(condition),
                then_branch: then_branch.clone(),
                else_branch: else_branch.clone(),
            },
            rules,
            theory,
            context,
        )?
        .map_or_else(
            || {
                simplify_child(
                    tactic,
                    computation,
                    then_branch,
                    |then_branch| Computation::If {
                        condition: condition.clone(),
                        then_branch: Box::new(then_branch),
                        else_branch: else_branch.clone(),
                    },
                    rules,
                    theory,
                    context,
                )?
                .map_or_else(
                    || {
                        simplify_child(
                            tactic,
                            computation,
                            else_branch,
                            |else_branch| Computation::If {
                                condition: condition.clone(),
                                then_branch: then_branch.clone(),
                                else_branch: Box::new(else_branch),
                            },
                            rules,
                            theory,
                            context,
                        )
                    },
                    |rewrite| Ok(Some(rewrite)),
                )
            },
            |rewrite| Ok(Some(rewrite)),
        ),
        Computation::SymbolEq { left, right } => simplify_child(
            tactic,
            computation,
            left,
            |left| Computation::SymbolEq {
                left: Box::new(left),
                right: right.clone(),
            },
            rules,
            theory,
            context,
        )?
        .map_or_else(
            || {
                simplify_child(
                    tactic,
                    computation,
                    right,
                    |right| Computation::SymbolEq {
                        left: left.clone(),
                        right: Box::new(right),
                    },
                    rules,
                    theory,
                    context,
                )
            },
            |rewrite| Ok(Some(rewrite)),
        ),
        Computation::ValueKind(child) => simplify_child(
            tactic,
            computation,
            child,
            |child| Computation::ValueKind(Box::new(child)),
            rules,
            theory,
            context,
        ),
        Computation::Lambda(_)
        | Computation::Nil
        | Computation::Ref(_)
        | Computation::Error(_)
        | Computation::Diverge
        | Computation::Var(_)
        | Computation::Quote(_) => Ok(None),
    }
}

fn simplify_child(
    tactic: &'static str,
    parent: &Computation,
    child: &Computation,
    rebuild: impl Fn(Computation) -> Computation,
    rules: &[ProofExpr],
    theory: &Theory,
    context: &Context,
) -> Result<Option<SimpRewrite>, ProofElaborationError> {
    let child_result = simplify_computation(tactic, child.clone(), rules, theory, context)?;
    if alpha_eq_computation(child, &child_result.result) {
        return Ok(None);
    }

    let parent = parent.clone();
    let result = rebuild(child_result.result.clone());
    let placeholder = fresh_rewrite_symbol(
        &Prop::Equal(parent.clone(), result.clone()),
        child,
        &child_result.result,
    );
    let template = Prop::Equal(parent.clone(), rebuild(Computation::Var(placeholder)));
    let mut trace = child_result.trace;
    trace.push_change("lift subcomputation", &parent, &result);

    Ok(Some(SimpRewrite {
        result,
        proof: Proof::Rewrite {
            equality: Box::new(child_result.proof),
            proof: Box::new(Proof::Refl(parent)),
            variable: placeholder,
            template,
        },
        trace,
    }))
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

fn tactic_specialize(
    assumption: Symbol,
    proof_expr: &ProofExpr,
    arguments: &[Computation],
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    if goal.context.contains_key(&assumption) {
        return Err(tactic_failed(
            "specialize",
            format!("assumption symbol {:?} is already in scope", assumption),
        ));
    }

    let proof = proof_expr_to_proof_in_context(proof_expr, theory, &goal.context)?;
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
                other => {
                    return Err(tactic_failed(
                        tactic,
                        explicit_argument_error_message(&other, argument, context),
                    ));
                }
            }
        }
    }

    finish_implications(tactic, proof, prop, theory, context, target)
}

fn apply_arguments_and_available_implications(
    tactic: &'static str,
    proof: Proof,
    prop: Prop,
    arguments: &[Computation],
    theory: &Theory,
    context: &Context,
) -> Result<(Proof, Prop), ProofElaborationError> {
    let (proof, prop) =
        apply_arguments_and_implications(tactic, proof, prop, arguments, theory, context, None)?;
    finish_available_implications(tactic, proof, prop, theory, context)
}

fn finish_available_implications(
    tactic: &'static str,
    mut proof: Proof,
    mut prop: Prop,
    theory: &Theory,
    context: &Context,
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

        let Ok(next_proof) = apply_available_premise(tactic, proof.clone(), &premise, context)
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
                    unavailable_premise_message(&premise, context),
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
    context: &Context,
) -> String {
    let argument_is_local_fact =
        matches!(argument, Computation::Var(symbol) if context.contains_key(symbol));
    let local_fact = match argument {
        Computation::Var(symbol) => context.get(symbol).map(|prop| {
            format!("\nargument {symbol:?} is a local proof/fact with proposition: {prop:?}")
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
                "next explicit argument: {argument:?}{local_fact}\n",
                "remaining premise: {premise:?}\n",
                "explicit proof-application arguments instantiate forall-bound computations only; ",
                "implication premises are taken from local assumptions and applied automatically ",
                "when available. Put the premise in scope with `intro`/`have`, then use `exact` ",
                "or `specialize` without passing that proof as an argument"
            ),
            argument = argument,
            local_fact = local_fact,
            premise = premise
        ),
        _ => format!(
            concat!(
                "too many explicit computation arguments; proof has no remaining forall binder ",
                "for argument {argument:?}{local_fact}\n",
                "current proposition: {prop:?}\n",
                "explicit proof-application arguments instantiate forall-bound computations only",
                "{local_fact_hint}"
            ),
            argument = argument,
            local_fact = local_fact,
            prop = prop,
            local_fact_hint = local_fact_hint
        ),
    }
}

fn apply_available_premise(
    tactic: &'static str,
    implication: Proof,
    premise: &Prop,
    context: &Context,
) -> Result<Proof, ProofElaborationError> {
    let premise_proof = available_prop_proof(premise, context)
        .map_err(|_| tactic_failed(tactic, unavailable_premise_message(premise, context)))?;

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

fn unavailable_premise_message(premise: &Prop, context: &Context) -> String {
    format!(
        "premise {:?} is not available; {}",
        premise,
        local_facts_message(context)
    )
}

fn local_facts_message(context: &Context) -> String {
    if context.is_empty() {
        return "no local facts are in scope".to_owned();
    }

    let mut facts = context.iter().collect::<Vec<_>>();
    facts.sort_by_key(|(symbol, _)| symbol.0);
    let facts = facts
        .into_iter()
        .map(|(symbol, prop)| format!("{symbol:?}: {prop:?}"))
        .collect::<Vec<_>>()
        .join("; ");

    format!("local facts in scope: {facts}")
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

fn tactic_obtain(
    existential_expr: &ProofExpr,
    witness: Symbol,
    assumption: Symbol,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
) -> Result<Proof, ProofElaborationError> {
    let existential = proof_expr_to_proof_in_context(existential_expr, theory, &goal.context)?;
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

    let conjunction = proof_expr_to_proof_in_context(conjunction_expr, theory, &goal.context)?;
    let Some(Prop::And(left, right)) = theory.proven_prop_in_context(&conjunction, &goal.context)
    else {
        return Err(tactic_failed("cases", "proof is not a conjunction"));
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

fn tactic_fold(
    definition: Name,
    rest: &[TacticExpr],
    theory: &Theory,
    goal: &Goal,
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
            format!("goal does not contain the definition body {:?}", body),
        ));
    };

    let folded_goal = Goal {
        context: goal.context.clone(),
        target: substitute_prop(&template, placeholder, &folded),
    };
    let proof = tactic_steps_to_proof(rest, theory, &folded_goal)?;

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
) -> Result<Proof, ProofElaborationError> {
    let (goal_variable, predicate, property) = value_induction_goal(&goal.target)?;

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
            "forall predicate is not an is-value predicate",
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
        symbol_case: Box::new(tactic_script_to_proof(symbol_case, theory, &symbol_goal)?),
        lambda_assumption,
        lambda_case: Box::new(tactic_script_to_proof(lambda_case, theory, &lambda_goal)?),
        nil_case: Box::new(tactic_script_to_proof(nil_case, theory, &nil_goal)?),
        head,
        tail,
        head_induction_hypothesis_assumption,
        tail_induction_hypothesis_assumption,
        cons_case: Box::new(tactic_script_to_proof(cons_case, theory, &cons_goal)?),
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

fn value_induction_goal(target: &Prop) -> Result<(Symbol, Prop, Prop), ProofElaborationError> {
    let Prop::ForAll { variable, body } = target else {
        return Err(tactic_failed("value-induction", "goal is not a forall"));
    };

    let Prop::Implies(predicate, body) = body.as_ref() else {
        return Err(tactic_failed(
            "value-induction",
            "forall body is not a predicate implication",
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

fn add_goal_context(
    error: ProofElaborationError,
    tactic_expr: &TacticExpr,
    target: &Prop,
) -> ProofElaborationError {
    match error {
        ProofElaborationError::TacticFailed { tactic, message } => {
            ProofElaborationError::TacticFailed {
                tactic,
                message: format!(
                    "{message}; while running {tactic_expr:?}; while proving {target:?}"
                ),
            }
        }
        ProofElaborationError::InSubproof { form, error } => ProofElaborationError::InSubproof {
            form,
            error: Box::new(add_goal_context(*error, tactic_expr, target)),
        },
        error => error,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forall_where;

    const THEOREM: Name = Name(1);
    const ALIAS_A: Name = Name(2);
    const ALIAS_B: Name = Name(3);
    const ALIAS_A_TO_NIL: Name = Name(4);
    const ALIAS_A_TO_ALIAS_B: Name = Name(5);
    const VALUE: Symbol = Symbol(10);
    const ASSUMED_EQUAL: Symbol = Symbol(11);
    const TARGET_VALUE: Symbol = Symbol(20);
    const TARGET_EQUAL: Symbol = Symbol(21);

    fn value_nil_rule() -> (Theory, Prop) {
        let premise = equal(Computation::Var(VALUE), Computation::Nil);
        let prop = forall_where(
            VALUE,
            is_value(Computation::Var(VALUE)),
            Prop::Implies(Box::new(premise.clone()), Box::new(premise.clone())),
        );
        let proof = Proof::ForAllIntro {
            variable: VALUE,
            proof: Box::new(Proof::ImpliesIntro {
                assumption: VALUE,
                premise: is_value(Computation::Var(VALUE)),
                proof: Box::new(Proof::ImpliesIntro {
                    assumption: ASSUMED_EQUAL,
                    premise,
                    proof: Box::new(Proof::Assume(ASSUMED_EQUAL)),
                }),
            }),
        };

        let mut theory = Theory::new();
        theory
            .define_theorem_from_proof_result(THEOREM, proof, prop.clone())
            .expect("test rule should be a valid theorem");

        (theory, prop)
    }

    fn alias_rewrite_theory() -> Theory {
        let mut theory = Theory::new();
        theory
            .define_computation_result(ALIAS_A, &Computation::Nil)
            .expect("alias A should be a closed computation");
        theory
            .define_computation_result(ALIAS_B, &Computation::Nil)
            .expect("alias B should be a closed computation");

        theory
            .define_theorem_from_proof_result(
                ALIAS_A_TO_NIL,
                Proof::Step(Computation::Ref(ALIAS_A)),
                equal(Computation::Ref(ALIAS_A), Computation::Nil),
            )
            .expect("alias A should equal nil by one unfolding step");
        theory
            .define_theorem_from_proof_result(
                ALIAS_A_TO_ALIAS_B,
                Proof::Trans(
                    Box::new(Proof::Step(Computation::Ref(ALIAS_A))),
                    Box::new(Proof::Symm(Box::new(Proof::Step(Computation::Ref(
                        ALIAS_B,
                    ))))),
                ),
                equal(Computation::Ref(ALIAS_A), Computation::Ref(ALIAS_B)),
            )
            .expect("alias A should equal alias B through nil");

        theory
    }

    #[test]
    fn instantiate_simp_rule_infers_arguments_and_uses_available_premises() {
        let (theory, prop) = value_nil_rule();
        let target = Computation::Var(TARGET_VALUE);
        let substitutions = HashMap::from([(VALUE, target.clone())]);
        let mut context = Context::new();
        context.insert(TARGET_VALUE, is_value(target.clone()));
        context.insert(TARGET_EQUAL, equal(target.clone(), Computation::Nil));

        let (_proof, proven) = instantiate_simp_rule(
            "simp",
            &ProofExpr::Known(THEOREM),
            Proof::Known(THEOREM),
            prop,
            &substitutions,
            &theory,
            &context,
        )
        .expect("rule instantiation should not fail")
        .expect("rule premises should be available");

        assert_eq!(
            proven,
            equal(Computation::Var(TARGET_VALUE), Computation::Nil)
        );
    }

    #[test]
    fn instantiate_simp_rule_skips_unavailable_premises() {
        let (theory, prop) = value_nil_rule();
        let target = Computation::Var(TARGET_VALUE);
        let substitutions = HashMap::from([(VALUE, target.clone())]);
        let mut context = Context::new();
        context.insert(TARGET_VALUE, is_value(target));

        assert_eq!(
            instantiate_simp_rule(
                "simp",
                &ProofExpr::Known(THEOREM),
                Proof::Known(THEOREM),
                prop,
                &substitutions,
                &theory,
                &context,
            ),
            Ok(None)
        );
    }

    #[test]
    fn simp_rewrite_uses_first_matching_rule() {
        let theory = alias_rewrite_theory();
        let rewrite = simp_rewrite(
            "simp",
            &Computation::Ref(ALIAS_A),
            &[
                ProofExpr::Known(ALIAS_A_TO_NIL),
                ProofExpr::Known(ALIAS_A_TO_ALIAS_B),
            ],
            &theory,
            &Context::new(),
        )
        .expect("simp rewrite should not fail")
        .expect("the first rule should match");

        assert_eq!(rewrite.result, Computation::Nil);
    }
}
