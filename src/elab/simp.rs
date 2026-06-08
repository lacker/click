//! Explicit simplifier tactics.

use std::collections::{HashMap, HashSet};

use crate::{
    Computation, Context, Lambda, ListCase, Proof, Prop, Symbol, Theory, alpha_eq_computation,
    alpha_eq_prop, substitute_prop,
};

use super::diagnostics::{
    compact_computation_source, compact_debug, compact_prop_source, context_diagnostic,
    prop_diagnostic, symbol_source,
};
use super::proof::{ProofElaborationError, proof_expr_to_proof_in_context};
use super::source::{PrettyEnv, ProofExpr};
use super::tactics::{
    Goal, available_prop_proof, finish_available_implications, fresh_rewrite_symbol,
    goal_not_equality_message, tactic_failed, trans_chain,
};

const SIMP_STEP_LIMIT: usize = 128;
const SIMP_RECURSION_LIMIT: usize = 256;
const SIMP_TRACE_LIMIT: usize = 32;

pub(super) fn tactic_simp(
    rules: &[ProofExpr],
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Equal(left, right) = &goal.target else {
        return Err(tactic_failed(
            "simp",
            goal_not_equality_message("simp_goal_not_equality", goal, pretty),
        ));
    };

    let goal_result = simplify_equality("simp", left, right, rules, theory, &goal.context, pretty)?;

    if !alpha_eq_computation(&goal_result.left.result, &goal_result.right.result) {
        return Err(tactic_failed(
            "simp",
            simp_failure_message(left, &goal_result.left, right, &goal_result.right, pretty),
        ));
    }

    Ok(goal_equality_proof_from_simplified(goal_result))
}

pub(super) fn tactic_simpa(
    rules: &[ProofExpr],
    proof_expr: Option<&ProofExpr>,
    theory: &Theory,
    goal: &Goal,
    pretty: &PrettyEnv,
) -> Result<Proof, ProofElaborationError> {
    let Prop::Equal(goal_left, goal_right) = &goal.target else {
        return Err(tactic_failed(
            "simpa",
            goal_not_equality_message("simpa_goal_not_equality", goal, pretty),
        ));
    };

    let goal_result = simplify_equality(
        "simpa",
        goal_left,
        goal_right,
        rules,
        theory,
        &goal.context,
        pretty,
    )?;
    let Some(proof_expr) = proof_expr else {
        if !alpha_eq_computation(&goal_result.left.result, &goal_result.right.result) {
            return Err(tactic_failed(
                "simpa",
                simp_failure_message(
                    goal_left,
                    &goal_result.left,
                    goal_right,
                    &goal_result.right,
                    pretty,
                ),
            ));
        }
        return Ok(goal_equality_proof_from_simplified(goal_result));
    };

    let proof = proof_expr_to_proof_in_context(proof_expr, theory, &goal.context, pretty)?;
    let prop = theory
        .proven_prop_in_context(&proof, &goal.context)
        .ok_or_else(|| {
            tactic_failed(
                "simpa",
                format!(
                    "using proof proves no proposition\n\
                     reason: simpa_using_proof_proves_no_proposition\n\
                     using_proof_expr.debug: {}\n\
                     {}\n\
                     {}",
                    compact_debug(proof_expr),
                    prop_diagnostic("goal", &goal.target, pretty),
                    context_diagnostic("context.locals", &goal.context, pretty)
                ),
            )
        })?;
    let (proof, prop) =
        finish_available_implications("simpa", proof, prop, theory, &goal.context, pretty)?;
    let Prop::Equal(proof_left, proof_right) = prop else {
        return Err(tactic_failed(
            "simpa",
            format!(
                "using proof proves {}, not an equality\n\
                 reason: simpa_using_proof_not_equality\n\
                 using_proof_expr.debug: {}\n\
                 {}\n\
                 {}\n\
                 {}",
                compact_prop_source(&prop, pretty),
                compact_debug(proof_expr),
                prop_diagnostic("using_proof", &prop, pretty),
                prop_diagnostic("goal", &goal.target, pretty),
                context_diagnostic("context.locals", &goal.context, pretty)
            ),
        ));
    };
    let proof_result = simplify_equality(
        "simpa",
        &proof_left,
        &proof_right,
        rules,
        theory,
        &goal.context,
        pretty,
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
            pretty,
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

    fn push_change(
        &mut self,
        label: impl Into<String>,
        before: &Computation,
        after: &Computation,
        pretty: &PrettyEnv,
    ) {
        self.push(format!(
            "{}: {} -> {}",
            label.into(),
            compact_computation_source(before, pretty),
            compact_computation_source(after, pretty)
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
    pretty: &PrettyEnv,
) -> Result<SimpEqualityResult, ProofElaborationError> {
    let mut left_budget = SimpBudget::new();
    let mut right_budget = SimpBudget::new();
    Ok(SimpEqualityResult {
        left: simplify_computation(
            tactic,
            left.clone(),
            rules,
            theory,
            context,
            &mut left_budget,
            pretty,
        )?,
        right: simplify_computation(
            tactic,
            right.clone(),
            rules,
            theory,
            context,
            &mut right_budget,
            pretty,
        )?,
    })
}

struct SimpBudget {
    remaining_recursions: usize,
}

impl SimpBudget {
    fn new() -> Self {
        Self {
            remaining_recursions: SIMP_RECURSION_LIMIT,
        }
    }

    fn consume(
        &mut self,
        tactic: &'static str,
        current: &Computation,
        pretty: &PrettyEnv,
    ) -> Result<(), ProofElaborationError> {
        let Some(remaining) = self.remaining_recursions.checked_sub(1) else {
            return Err(tactic_failed(
                tactic,
                format!(
                    "simplification recursion exceeded {SIMP_RECURSION_LIMIT} recursive calls \
                     while simplifying {}\n\
                     this usually means a simp rule is oriented as an expansion that keeps \
                     introducing another reducible subterm; use explicit `rewrite`, `eval`, or \
                     `fold` for one-shot expansion, or orient simp rules toward canonical forms",
                    compact_computation_source(current, pretty)
                ),
            ));
        };

        self.remaining_recursions = remaining;
        Ok(())
    }
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
    budget: &mut SimpBudget,
    pretty: &PrettyEnv,
) -> Result<SimpResult, ProofElaborationError> {
    budget.consume(tactic, &original, pretty)?;

    let mut current = original.clone();
    let mut proofs = Vec::new();
    let mut trace = SimpTrace::default();
    let mut seen = vec![current.clone()];

    for _ in 0..SIMP_STEP_LIMIT {
        if let Some(rewrite) = simp_rewrite(tactic, &current, rules, theory, context, pretty)? {
            trace.extend(rewrite.trace);
            proofs.push(rewrite.proof);
            current = rewrite.result;
            record_simp_state(tactic, &mut seen, &current, &trace, pretty)?;
            continue;
        }

        if let Some(rewrite) = simp_child(tactic, &current, rules, theory, context, budget, pretty)?
        {
            trace.extend(rewrite.trace);
            proofs.push(rewrite.proof);
            current = rewrite.result;
            record_simp_state(tactic, &mut seen, &current, &trace, pretty)?;
            continue;
        }

        match theory.reduce_in_context(&current, context) {
            crate::Step::Reduced(next) => {
                trace.push_change("kernel reduction", &current, &next, pretty);
                proofs.push(Proof::Step(current));
                current = next;
                record_simp_state(tactic, &mut seen, &current, &trace, pretty)?;
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
    pretty: &PrettyEnv,
) -> Result<Option<SimpRewrite>, ProofElaborationError> {
    for (rule_index, rule) in rules.iter().enumerate() {
        if let Some(rewrite) =
            simp_rewrite_with_rule(tactic, rule_index, rule, target, theory, context, pretty)?
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
    pretty: &PrettyEnv,
) -> Result<Option<SimpRewrite>, ProofElaborationError> {
    let proof = proof_expr_to_proof_in_context(rule, theory, context, pretty)?;
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

        let Some((proof, proven)) = instantiate_simp_rule(
            tactic,
            rule,
            proof,
            prop,
            &substitutions,
            theory,
            context,
            pretty,
        )?
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
                            simp_expansion_rule_message(rule_index, rule, target, &right, pretty),
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
                    pretty,
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
    pretty: &PrettyEnv,
) -> Result<Option<(Proof, Prop)>, ProofElaborationError> {
    loop {
        match prop {
            Prop::ForAll { variable, body } => {
                let Some(argument) = substitutions.get(&variable).cloned() else {
                    return Err(tactic_failed(
                        tactic,
                        format!(
                            "could not infer argument {} for rule {rule:?}\n\
                             reason: simp_could_not_infer_argument\n\
                             variable.debug: {:?}",
                            symbol_source(variable, pretty),
                            variable
                        ),
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
                let Ok(premise_proof) = available_prop_proof(&premise, context, pretty) else {
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
    pretty: &PrettyEnv,
) -> String {
    format!(
        "simplified goal, but the sides still differ\n\
         reason: simp_normal_forms_differ\n\
         left original: {}\n\
         left result: {}\n\
         left.source: {}\n\
         left.result.source: {}\n\
         left.debug: {}\n\
         left.result.debug: {}\n\
         left steps:\n{}\n\
         right original: {}\n\
         right result: {}\n\
         right.source: {}\n\
         right.result.source: {}\n\
         right.debug: {}\n\
         right.result.debug: {}\n\
         right steps:\n{}",
        compact_computation_source(left_original, pretty),
        compact_computation_source(&left_result.result, pretty),
        compact_computation_source(left_original, pretty),
        compact_computation_source(&left_result.result, pretty),
        compact_debug(left_original),
        compact_debug(&left_result.result),
        format_simp_trace(&left_result.trace),
        compact_computation_source(right_original, pretty),
        compact_computation_source(&right_result.result, pretty),
        compact_computation_source(right_original, pretty),
        compact_computation_source(&right_result.result, pretty),
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
    pretty: &PrettyEnv,
) -> String {
    format!(
        "simplified goal and using proof, but they do not match\n\
         reason: simpa_normal_forms_differ\n\
         goal left original: {}\n\
         goal left result: {}\n\
         goal.left.source: {}\n\
         goal.left.result.source: {}\n\
         goal.left.debug: {}\n\
         goal.left.result.debug: {}\n\
         goal left steps:\n{}\n\
         goal right original: {}\n\
         goal right result: {}\n\
         goal.right.source: {}\n\
         goal.right.result.source: {}\n\
         goal.right.debug: {}\n\
         goal.right.result.debug: {}\n\
         goal right steps:\n{}\n\
         using left original: {}\n\
         using left result: {}\n\
         using.left.source: {}\n\
         using.left.result.source: {}\n\
         using.left.debug: {}\n\
         using.left.result.debug: {}\n\
         using left steps:\n{}\n\
         using right original: {}\n\
         using right result: {}\n\
         using.right.source: {}\n\
         using.right.result.source: {}\n\
         using.right.debug: {}\n\
         using.right.result.debug: {}\n\
         using right steps:\n{}",
        compact_computation_source(goal_left_original, pretty),
        compact_computation_source(&goal_left_result.result, pretty),
        compact_computation_source(goal_left_original, pretty),
        compact_computation_source(&goal_left_result.result, pretty),
        compact_debug(goal_left_original),
        compact_debug(&goal_left_result.result),
        format_simp_trace(&goal_left_result.trace),
        compact_computation_source(goal_right_original, pretty),
        compact_computation_source(&goal_right_result.result, pretty),
        compact_computation_source(goal_right_original, pretty),
        compact_computation_source(&goal_right_result.result, pretty),
        compact_debug(goal_right_original),
        compact_debug(&goal_right_result.result),
        format_simp_trace(&goal_right_result.trace),
        compact_computation_source(proof_left_original, pretty),
        compact_computation_source(&proof_left_result.result, pretty),
        compact_computation_source(proof_left_original, pretty),
        compact_computation_source(&proof_left_result.result, pretty),
        compact_debug(proof_left_original),
        compact_debug(&proof_left_result.result),
        format_simp_trace(&proof_left_result.trace),
        compact_computation_source(proof_right_original, pretty),
        compact_computation_source(&proof_right_result.result, pretty),
        compact_computation_source(proof_right_original, pretty),
        compact_computation_source(&proof_right_result.result, pretty),
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
    pretty: &PrettyEnv,
) -> Result<(), ProofElaborationError> {
    if let Some(first_seen_step) = seen
        .iter()
        .position(|seen| alpha_eq_computation(seen, current))
    {
        return Err(tactic_failed(
            tactic,
            simp_cycle_message(first_seen_step, current, trace, pretty),
        ));
    }

    seen.push(current.clone());
    Ok(())
}

fn simp_cycle_message(
    first_seen_step: usize,
    repeated: &Computation,
    trace: &SimpTrace,
    pretty: &PrettyEnv,
) -> String {
    format!(
        "simplification cycle detected after {} steps\n\
         reason: simp_cycle\n\
         repeated term first seen after {first_seen_step} steps: {}\n\
         repeated.source: {}\n\
         repeated.debug: {}\n\
         this usually means a simp rule is oriented as an expansion that kernel reduction can undo; \
         use explicit `rewrite`, `eval`, or `fold` for one-shot expansion, or orient simp rules toward canonical forms\n\
         steps:\n{}",
        trace.total_steps(),
        compact_computation_source(repeated, pretty),
        compact_computation_source(repeated, pretty),
        compact_debug(repeated),
        format_simp_trace(trace)
    )
}

fn simp_expansion_rule_message(
    rule_index: usize,
    rule: &ProofExpr,
    target: &Computation,
    expanded: &Computation,
    pretty: &PrettyEnv,
) -> String {
    let fold_hint = match expanded {
        Computation::Ref(_) => " use `(fold <definition>)` for this source-level name,".to_string(),
        _ => " use `fold` for named definitions,".to_string(),
    };

    format!(
        "simp rule {} ({}) is oriented as an expansion\n\
         reason: simp_expansion_rule\n\
         rule_expr.debug: {}\n\
         target.source: {}\n\
         target.debug: {}\n\
         expanded.source: {}\n\
         expanded.debug: {}\n\
         rewriting {} to {} is immediately undone by kernel reduction;{} \
         or use explicit `rewrite`/`eval` for one-shot expansion; simp rules should move toward canonical forms",
        rule_index + 1,
        compact_debug(rule),
        compact_debug(rule),
        compact_computation_source(target, pretty),
        compact_debug(target),
        compact_computation_source(expanded, pretty),
        compact_debug(expanded),
        compact_computation_source(target, pretty),
        compact_computation_source(expanded, pretty),
        fold_hint
    )
}

fn simp_child(
    tactic: &'static str,
    computation: &Computation,
    rules: &[ProofExpr],
    theory: &Theory,
    context: &Context,
    budget: &mut SimpBudget,
    pretty: &PrettyEnv,
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
            budget,
            pretty,
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
                    budget,
                    pretty,
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
            budget,
            pretty,
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
                    budget,
                    pretty,
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
            budget,
            pretty,
        ),
        Computation::Tail(child) => simplify_child(
            tactic,
            computation,
            child,
            |child| Computation::Tail(Box::new(child)),
            rules,
            theory,
            context,
            budget,
            pretty,
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
            budget,
            pretty,
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
                    budget,
                    pretty,
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
            budget,
            pretty,
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
                    budget,
                    pretty,
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
                            budget,
                            pretty,
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
            budget,
            pretty,
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
                    budget,
                    pretty,
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
            budget,
            pretty,
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
    budget: &mut SimpBudget,
    pretty: &PrettyEnv,
) -> Result<Option<SimpRewrite>, ProofElaborationError> {
    let child_result = simplify_computation(
        tactic,
        child.clone(),
        rules,
        theory,
        context,
        budget,
        pretty,
    )?;
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
    trace.push_change("lift subcomputation", &parent, &result, pretty);

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Name, equal, forall_where, is_value};

    const THEOREM: Name = Name(1);
    const ALIAS_A: Name = Name(2);
    const ALIAS_B: Name = Name(3);
    const ALIAS_A_TO_NIL: Name = Name(4);
    const ALIAS_A_TO_ALIAS_B: Name = Name(5);
    const VALUE: Symbol = Symbol(10);
    const ASSUMED_EQUAL: Symbol = Symbol(11);
    const TARGET_VALUE: Symbol = Symbol(20);
    const TARGET_EQUAL: Symbol = Symbol(21);
    const RECURSIVE_EXPANSION_RULE: Symbol = Symbol(22);

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
        let pretty = PrettyEnv::new();

        let (_proof, proven) = instantiate_simp_rule(
            "simp",
            &ProofExpr::Known(THEOREM),
            Proof::Known(THEOREM),
            prop,
            &substitutions,
            &theory,
            &context,
            &pretty,
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
        let pretty = PrettyEnv::new();

        assert_eq!(
            instantiate_simp_rule(
                "simp",
                &ProofExpr::Known(THEOREM),
                Proof::Known(THEOREM),
                prop,
                &substitutions,
                &theory,
                &context,
                &pretty,
            ),
            Ok(None)
        );
    }

    #[test]
    fn simp_rewrite_uses_first_matching_rule() {
        let theory = alias_rewrite_theory();
        let pretty = PrettyEnv::new();
        let rewrite = simp_rewrite(
            "simp",
            &Computation::Ref(ALIAS_A),
            &[
                ProofExpr::Known(ALIAS_A_TO_NIL),
                ProofExpr::Known(ALIAS_A_TO_ALIAS_B),
            ],
            &theory,
            &Context::new(),
            &pretty,
        )
        .expect("simp rewrite should not fail")
        .expect("the first rule should match");

        assert_eq!(rewrite.result, Computation::Nil);
    }

    #[test]
    fn simp_reports_recursive_expansion_before_stack_overflow() {
        let target = Computation::Var(TARGET_VALUE);
        let expansion = Computation::Cons {
            head: Box::new(Computation::Nil),
            tail: Box::new(target.clone()),
        };
        let mut context = Context::new();
        context.insert(RECURSIVE_EXPANSION_RULE, equal(target.clone(), expansion));
        let pretty = PrettyEnv::new();

        let mut budget = SimpBudget::new();
        let result = simplify_computation(
            "simp",
            target,
            &[ProofExpr::Assume(RECURSIVE_EXPANSION_RULE)],
            &Theory::new(),
            &context,
            &mut budget,
            &pretty,
        );

        let Err(ProofElaborationError::TacticFailed { tactic, message }) = result else {
            panic!("recursive expansion should fail as a tactic error");
        };

        assert_eq!(tactic, "simp");
        assert!(message.contains("simplification recursion exceeded"));
        assert!(message.contains("recursive calls"));
        assert!(message.contains("oriented as an expansion"));
        assert!(message.contains("rewrite"));
        assert!(message.contains("eval"));
        assert!(message.contains("fold"));
        assert!(message.contains("canonical forms"));
    }
}
