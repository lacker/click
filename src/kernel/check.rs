use std::collections::HashSet;

use super::{
    calculus::*,
    theory::{Bindings, ProofContext},
};

pub fn check(proof: &Proof, prop: &Prop) -> bool {
    check_in_context(proof, prop, &ProofContext::new())
}

pub fn check_in_context(proof: &Proof, prop: &Prop, context: &ProofContext) -> bool {
    check_in_bindings_and_context(proof, prop, &Bindings::new(), context)
}

pub(crate) fn check_in_bindings(proof: &Proof, prop: &Prop, bindings: &Bindings) -> bool {
    check_in_bindings_and_context(proof, prop, bindings, &ProofContext::new())
}

pub(super) fn check_in_bindings_and_context(
    proof: &Proof,
    prop: &Prop,
    bindings: &Bindings,
    context: &ProofContext,
) -> bool {
    proven_prop(proof, bindings, context).is_some_and(|proven| alpha_eq_prop(&proven, prop))
}

pub fn alpha_eq_prop(left: &Prop, right: &Prop) -> bool {
    alpha_eq_prop_in_context(left, right, &mut Vec::new())
}

pub fn alpha_eq_computation(left: &Computation, right: &Computation) -> bool {
    alpha_eq_computation_in_context(left, right, &mut Vec::new())
}

fn alpha_eq_prop_in_context(
    left: &Prop,
    right: &Prop,
    bindings: &mut Vec<(Symbol, Symbol)>,
) -> bool {
    match (left, right) {
        (Prop::Absurd, Prop::Absurd) => true,
        (Prop::Equal(left_left, left_right), Prop::Equal(right_left, right_right)) => {
            alpha_eq_computation_in_context(left_left, right_left, bindings)
                && alpha_eq_computation_in_context(left_right, right_right, bindings)
        }
        (Prop::IsValue(left), Prop::IsValue(right))
        | (Prop::IsList(left), Prop::IsList(right))
        | (Prop::IsEffect(left), Prop::IsEffect(right))
        | (Prop::IsOutcome(left), Prop::IsOutcome(right)) => {
            alpha_eq_computation_in_context(left, right, bindings)
        }
        (
            Prop::Implies(left_premise, left_conclusion),
            Prop::Implies(right_premise, right_conclusion),
        )
        | (Prop::And(left_premise, left_conclusion), Prop::And(right_premise, right_conclusion))
        | (Prop::Or(left_premise, left_conclusion), Prop::Or(right_premise, right_conclusion)) => {
            alpha_eq_prop_in_context(left_premise, right_premise, bindings)
                && alpha_eq_prop_in_context(left_conclusion, right_conclusion, bindings)
        }
        (
            Prop::ForAll {
                variable: left_variable,
                body: left_body,
            },
            Prop::ForAll {
                variable: right_variable,
                body: right_body,
            },
        )
        | (
            Prop::Exists {
                variable: left_variable,
                body: left_body,
            },
            Prop::Exists {
                variable: right_variable,
                body: right_body,
            },
        ) => alpha_eq_binder(*left_variable, *right_variable, bindings, |bindings| {
            alpha_eq_prop_in_context(left_body, right_body, bindings)
        }),
        _ => false,
    }
}

fn alpha_eq_computation_in_context(
    left: &Computation,
    right: &Computation,
    bindings: &mut Vec<(Symbol, Symbol)>,
) -> bool {
    match (left, right) {
        (
            Computation::Apply {
                function: left_function,
                argument: left_argument,
            },
            Computation::Apply {
                function: right_function,
                argument: right_argument,
            },
        ) => {
            alpha_eq_computation_in_context(left_function, right_function, bindings)
                && alpha_eq_computation_in_context(left_argument, right_argument, bindings)
        }
        (Computation::Lambda(left), Computation::Lambda(right)) => {
            alpha_eq_binder(left.parameter, right.parameter, bindings, |bindings| {
                alpha_eq_computation_in_context(&left.body, &right.body, bindings)
            })
        }
        (Computation::Nil, Computation::Nil) => true,
        (Computation::Bv32(left), Computation::Bv32(right)) => left == right,
        (
            Computation::Cons {
                head: left_head,
                tail: left_tail,
            },
            Computation::Cons {
                head: right_head,
                tail: right_tail,
            },
        ) => {
            alpha_eq_computation_in_context(left_head, right_head, bindings)
                && alpha_eq_computation_in_context(left_tail, right_tail, bindings)
        }
        (Computation::Head(left), Computation::Head(right))
        | (Computation::Tail(left), Computation::Tail(right)) => {
            alpha_eq_computation_in_context(left, right, bindings)
        }
        (Computation::ListCase(left), Computation::ListCase(right)) => {
            alpha_eq_computation_in_context(&left.list, &right.list, bindings)
                && alpha_eq_computation_in_context(&left.nil, &right.nil, bindings)
                && alpha_eq_binder(left.cons, right.cons, bindings, |bindings| {
                    alpha_eq_computation_in_context(&left.cons_case, &right.cons_case, bindings)
                })
        }
        (
            Computation::If {
                condition: left_condition,
                then_branch: left_then_branch,
                else_branch: left_else_branch,
            },
            Computation::If {
                condition: right_condition,
                then_branch: right_then_branch,
                else_branch: right_else_branch,
            },
        ) => {
            alpha_eq_computation_in_context(left_condition, right_condition, bindings)
                && alpha_eq_computation_in_context(left_then_branch, right_then_branch, bindings)
                && alpha_eq_computation_in_context(left_else_branch, right_else_branch, bindings)
        }
        (
            Computation::SymbolEq {
                left: left_left,
                right: left_right,
            },
            Computation::SymbolEq {
                left: right_left,
                right: right_right,
            },
        ) => {
            alpha_eq_computation_in_context(left_left, right_left, bindings)
                && alpha_eq_computation_in_context(left_right, right_right, bindings)
        }
        (
            Computation::Bv32Eq {
                left: left_left,
                right: left_right,
            },
            Computation::Bv32Eq {
                left: right_left,
                right: right_right,
            },
        )
        | (
            Computation::Bv32Add {
                left: left_left,
                right: left_right,
            },
            Computation::Bv32Add {
                left: right_left,
                right: right_right,
            },
        )
        | (
            Computation::Bv32Slt {
                left: left_left,
                right: left_right,
            },
            Computation::Bv32Slt {
                left: right_left,
                right: right_right,
            },
        )
        | (
            Computation::Bv32SignedAddOverflows {
                left: left_left,
                right: left_right,
            },
            Computation::Bv32SignedAddOverflows {
                left: right_left,
                right: right_right,
            },
        ) => {
            alpha_eq_computation_in_context(left_left, right_left, bindings)
                && alpha_eq_computation_in_context(left_right, right_right, bindings)
        }
        (Computation::ValueKind(left), Computation::ValueKind(right)) => {
            alpha_eq_computation_in_context(left, right, bindings)
        }
        (Computation::Ref(left), Computation::Ref(right)) => left == right,
        (Computation::Error(left), Computation::Error(right)) => left == right,
        (Computation::Diverge, Computation::Diverge) => true,
        (Computation::Var(left), Computation::Var(right)) => {
            alpha_eq_symbol(*left, *right, bindings)
        }
        (Computation::Quote(left), Computation::Quote(right)) => left == right,
        _ => false,
    }
}

fn alpha_eq_binder<T>(
    left: Symbol,
    right: Symbol,
    bindings: &mut Vec<(Symbol, Symbol)>,
    compare_body: impl FnOnce(&mut Vec<(Symbol, Symbol)>) -> T,
) -> T {
    bindings.push((left, right));
    let result = compare_body(bindings);
    bindings.pop();
    result
}

fn alpha_eq_symbol(left: Symbol, right: Symbol, bindings: &[(Symbol, Symbol)]) -> bool {
    match (
        alpha_bound_position(left, bindings, |(left, _)| *left),
        alpha_bound_position(right, bindings, |(_, right)| *right),
    ) {
        (Some(left), Some(right)) => left == right,
        (None, None) => left == right,
        _ => false,
    }
}

fn alpha_bound_position(
    symbol: Symbol,
    bindings: &[(Symbol, Symbol)],
    select: impl Fn(&(Symbol, Symbol)) -> Symbol,
) -> Option<usize> {
    bindings
        .iter()
        .rposition(|binding| select(binding) == symbol)
}

pub(super) fn proven_prop(
    proof: &Proof,
    bindings: &Bindings,
    context: &ProofContext,
) -> Option<Prop> {
    proven_prop_in_context(proof, bindings, context)
}

pub(super) fn step_in_bindings_and_context(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
) -> Step {
    step_for_proof(computation, bindings, context)
}

pub(super) fn step_contextual_in_bindings_and_context(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
) -> Step {
    step_contextual_for_proof(computation, bindings, context)
}

fn proven_prop_in_context(
    proof: &Proof,
    bindings: &Bindings,
    context: &ProofContext,
) -> Option<Prop> {
    match proof {
        Proof::Known(name) => bindings.theorem(*name).cloned(),
        Proof::Assume(symbol) => context.get(symbol).cloned(),
        Proof::Primitive(prop) => primitive_prop_holds(prop, context).then_some(prop.clone()),
        Proof::Refl(computation) => Some(Prop::Equal(computation.clone(), computation.clone())),
        Proof::Symm(proof) => match proven_prop_in_context(proof, bindings, context)? {
            Prop::Equal(left, right) => Some(Prop::Equal(right, left)),
            _ => None,
        },
        Proof::Trans(first, second) => {
            match (
                proven_prop_in_context(first, bindings, context)?,
                proven_prop_in_context(second, bindings, context)?,
            ) {
                (Prop::Equal(left, middle), Prop::Equal(second_middle, right))
                    if alpha_eq_computation(&middle, &second_middle) =>
                {
                    Some(Prop::Equal(left, right))
                }
                _ => None,
            }
        }
        Proof::SymbolEqTrueElim(proof) => {
            symbol_eq_true_elim(proven_prop_in_context(proof, bindings, context)?)
        }
        Proof::SymbolEqTrueLeftIsSymbol(proof) => {
            symbol_eq_true_left_is_symbol(proven_prop_in_context(proof, bindings, context)?)
        }
        Proof::SymbolEqTrueRightIsSymbol(proof) => {
            symbol_eq_true_right_is_symbol(proven_prop_in_context(proof, bindings, context)?)
        }
        Proof::SymbolEqResultBool(proof) => {
            symbol_eq_result_bool(proven_prop_in_context(proof, bindings, context)?, context)
        }
        Proof::IfTrueWithFalseElseCondition(proof) => {
            if_true_with_false_else_condition(proven_prop_in_context(proof, bindings, context)?)
        }
        Proof::IfTrueWithFalseElseThen(proof) => {
            if_true_with_false_else_then(proven_prop_in_context(proof, bindings, context)?)
        }
        Proof::IfValueWithEffectThenConditionFalse(proof) => {
            if_value_with_effect_then_condition_false(proven_prop_in_context(
                proof, bindings, context,
            )?)
        }
        Proof::IfValueWithEffectThenElse(proof) => {
            if_value_with_effect_then_else(proven_prop_in_context(proof, bindings, context)?)
        }
        Proof::IfValueConditionBool(proof) => {
            if_value_condition_bool(proven_prop_in_context(proof, bindings, context)?, context)
        }
        Proof::ApplyValueArgument { variable, proof } => apply_value_argument(
            *variable,
            proven_prop_in_context(proof, bindings, context)?,
            context,
        ),
        Proof::DistinctOutcomes(proof) => {
            distinct_outcomes(proven_prop_in_context(proof, bindings, context)?, context)
        }
        Proof::ValueNonSymbolNonLambdaNonBv32IsList {
            value,
            not_symbol,
            not_lambda,
            not_bv32,
        } => value_non_symbol_non_lambda_non_bv32_is_list(
            proven_prop_in_context(value, bindings, context)?,
            proven_prop_in_context(not_symbol, bindings, context)?,
            proven_prop_in_context(not_lambda, bindings, context)?,
            proven_prop_in_context(not_bv32, bindings, context)?,
        ),
        Proof::AbsurdElim { absurd, prop } => {
            let Prop::Absurd = proven_prop_in_context(absurd, bindings, context)? else {
                return None;
            };
            Some(prop.clone())
        }
        Proof::Step(computation) => match step_for_proof(computation, bindings, context) {
            Step::Reduced(reduced) => Some(Prop::Equal(computation.clone(), reduced)),
            Step::Normal => None,
        },
        Proof::Steps(computations) => proven_steps(computations, bindings, context),
        Proof::ContextSteps(computations) => proven_context_steps(computations, bindings, context),
        Proof::Rewrite {
            equality,
            proof,
            variable,
            template,
        } => {
            let Prop::Equal(left, right) = proven_prop_in_context(equality, bindings, context)?
            else {
                return None;
            };

            let left_instance = substitute_prop(template, *variable, &left);
            if !alpha_eq_prop(
                &proven_prop_in_context(proof, bindings, context)?,
                &left_instance,
            ) {
                return None;
            }

            Some(substitute_prop(template, *variable, &right))
        }
        Proof::ListInduction {
            variable,
            property,
            base,
            head,
            tail,
            induction_hypothesis_assumption,
            step,
        } => {
            let symbols = ListInductionSymbols {
                variable: *variable,
                head: *head,
                tail: *tail,
                induction_hypothesis_assumption: *induction_hypothesis_assumption,
            };

            prove_list_induction(bindings, context, symbols, property, base, step)
        }
        Proof::ValueInduction {
            variable,
            property,
            symbol_assumption,
            symbol_case,
            lambda_assumption,
            lambda_case,
            bv32_assumption,
            bv32_case,
            nil_case,
            head,
            tail,
            head_induction_hypothesis_assumption,
            tail_induction_hypothesis_assumption,
            cons_case,
        } => {
            let symbols = ValueInductionSymbols {
                variable: *variable,
                symbol_assumption: *symbol_assumption,
                lambda_assumption: *lambda_assumption,
                bv32_assumption: *bv32_assumption,
                head: *head,
                tail: *tail,
                head_induction_hypothesis_assumption: *head_induction_hypothesis_assumption,
                tail_induction_hypothesis_assumption: *tail_induction_hypothesis_assumption,
            };
            let cases = ValueInductionCases {
                symbol_case,
                lambda_case,
                bv32_case,
                nil_case,
                cons_case,
            };

            prove_value_induction(bindings, context, symbols, property, cases)
        }
        Proof::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => {
            let mut context = context.clone();
            context.insert(*assumption, premise.clone());
            let conclusion = proven_prop_in_context(proof, bindings, &context)?;
            Some(Prop::Implies(
                Box::new(premise.clone()),
                Box::new(conclusion),
            ))
        }
        Proof::ImpliesElim {
            implication,
            premise,
        } => {
            let premise = proven_prop_in_context(premise, bindings, context)?;
            match proven_prop_in_context(implication, bindings, context)? {
                Prop::Implies(expected_premise, conclusion)
                    if alpha_eq_prop(&expected_premise, &premise) =>
                {
                    Some(*conclusion)
                }
                _ => None,
            }
        }
        Proof::ForAllIntro { variable, proof } => {
            if context_mentions_symbol(context, *variable) {
                return None;
            }

            let body = proven_prop_in_context(proof, bindings, context)?;
            Some(forall(*variable, body))
        }
        Proof::ForAllElim { forall, argument } => {
            match proven_prop_in_context(forall, bindings, context)? {
                Prop::ForAll { variable, body } => Some(substitute_prop(&body, variable, argument)),
                _ => None,
            }
        }
        Proof::ExistsIntro {
            variable,
            body,
            witness,
            proof,
        } => {
            let witness_body = substitute_prop(body, *variable, witness);
            if !alpha_eq_prop(
                &proven_prop_in_context(proof, bindings, context)?,
                &witness_body,
            ) {
                return None;
            }

            Some(exists(*variable, body.clone()))
        }
        Proof::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        } => match proven_prop_in_context(existential, bindings, context)? {
            Prop::Exists { variable, body } => {
                let existential = Prop::Exists {
                    variable,
                    body: body.clone(),
                };
                let has_witness_assumption = matches!(body.as_ref(), Prop::And(_, _));
                if prop_mentions_symbol(&existential, *witness)
                    || context_mentions_symbol(context, *witness)
                    || (has_witness_assumption
                        && (context.contains_key(witness) || assumption == witness))
                {
                    return None;
                }

                let witness_var = Computation::Var(*witness);
                let mut context = context.clone();
                match body.as_ref() {
                    Prop::And(left, right) => {
                        context.insert(*witness, substitute_prop(left, variable, &witness_var));
                        context.insert(*assumption, substitute_prop(right, variable, &witness_var));
                    }
                    _ => {
                        context.insert(*assumption, substitute_prop(&body, variable, &witness_var));
                    }
                }
                let conclusion = proven_prop_in_context(proof, bindings, &context)?;

                if prop_mentions_symbol(&conclusion, *witness) {
                    None
                } else {
                    Some(conclusion)
                }
            }
            _ => None,
        },
        Proof::AndIntro(left, right) => Some(Prop::And(
            Box::new(proven_prop_in_context(left, bindings, context)?),
            Box::new(proven_prop_in_context(right, bindings, context)?),
        )),
        Proof::AndElimLeft(proof) => match proven_prop_in_context(proof, bindings, context)? {
            Prop::And(left, _) => Some(*left),
            _ => None,
        },
        Proof::AndElimRight(proof) => match proven_prop_in_context(proof, bindings, context)? {
            Prop::And(_, right) => Some(*right),
            _ => None,
        },
        Proof::OrIntroLeft { proof, right } => Some(Prop::Or(
            Box::new(proven_prop_in_context(proof, bindings, context)?),
            Box::new(right.clone()),
        )),
        Proof::OrIntroRight { left, proof } => Some(Prop::Or(
            Box::new(left.clone()),
            Box::new(proven_prop_in_context(proof, bindings, context)?),
        )),
        Proof::OrElim {
            disjunction,
            left_assumption,
            left_proof,
            right_assumption,
            right_proof,
        } => match proven_prop_in_context(disjunction, bindings, context)? {
            Prop::Or(left, right) => {
                let mut left_context = context.clone();
                left_context.insert(*left_assumption, *left);
                let left_conclusion = proven_prop_in_context(left_proof, bindings, &left_context)?;

                let mut right_context = context.clone();
                right_context.insert(*right_assumption, *right);
                let right_conclusion =
                    proven_prop_in_context(right_proof, bindings, &right_context)?;

                if alpha_eq_prop(&left_conclusion, &right_conclusion) {
                    Some(left_conclusion)
                } else {
                    None
                }
            }
            _ => None,
        },
    }
}

fn symbol_eq_true_elim(prop: Prop) -> Option<Prop> {
    match prop {
        Prop::Equal(Computation::SymbolEq { left, right }, Computation::Quote(TRUE_SYMBOL)) => {
            Some(Prop::Equal(*left, *right))
        }
        _ => None,
    }
}

fn symbol_eq_true_left_is_symbol(prop: Prop) -> Option<Prop> {
    match prop {
        Prop::Equal(Computation::SymbolEq { left, .. }, Computation::Quote(TRUE_SYMBOL)) => {
            Some(value_kind_is_kind(*left, SYMBOL_KIND_SYMBOL))
        }
        _ => None,
    }
}

fn symbol_eq_true_right_is_symbol(prop: Prop) -> Option<Prop> {
    match prop {
        Prop::Equal(Computation::SymbolEq { right, .. }, Computation::Quote(TRUE_SYMBOL)) => {
            Some(value_kind_is_kind(*right, SYMBOL_KIND_SYMBOL))
        }
        _ => None,
    }
}

fn symbol_eq_result_bool(prop: Prop, context: &ProofContext) -> Option<Prop> {
    match prop {
        Prop::Equal(Computation::SymbolEq { .. }, value)
            if computation_is_known_value(&value, context) =>
        {
            Some(is_bool(value))
        }
        _ => None,
    }
}

fn if_true_with_false_else_condition(prop: Prop) -> Option<Prop> {
    match prop {
        Prop::Equal(
            Computation::If {
                condition,
                then_branch: _,
                else_branch,
            },
            Computation::Quote(TRUE_SYMBOL),
        ) if alpha_eq_computation(else_branch.as_ref(), &Computation::Quote(FALSE_SYMBOL)) => {
            Some(Prop::Equal(*condition, Computation::Quote(TRUE_SYMBOL)))
        }
        _ => None,
    }
}

fn if_true_with_false_else_then(prop: Prop) -> Option<Prop> {
    match prop {
        Prop::Equal(
            Computation::If {
                condition: _,
                then_branch,
                else_branch,
            },
            Computation::Quote(TRUE_SYMBOL),
        ) if alpha_eq_computation(else_branch.as_ref(), &Computation::Quote(FALSE_SYMBOL)) => {
            Some(Prop::Equal(*then_branch, Computation::Quote(TRUE_SYMBOL)))
        }
        _ => None,
    }
}

fn if_value_with_effect_then_condition_false(prop: Prop) -> Option<Prop> {
    match prop {
        Prop::Equal(
            Computation::If {
                condition,
                then_branch,
                else_branch: _,
            },
            value,
        ) if then_branch.as_effect().is_some() && value.as_value().is_some() => {
            Some(Prop::Equal(*condition, Computation::Quote(FALSE_SYMBOL)))
        }
        _ => None,
    }
}

fn if_value_with_effect_then_else(prop: Prop) -> Option<Prop> {
    match prop {
        Prop::Equal(
            Computation::If {
                condition: _,
                then_branch,
                else_branch,
            },
            value,
        ) if then_branch.as_effect().is_some() && value.as_value().is_some() => {
            Some(Prop::Equal(*else_branch, value))
        }
        _ => None,
    }
}

fn if_value_condition_bool(prop: Prop, context: &ProofContext) -> Option<Prop> {
    match prop {
        Prop::Equal(
            Computation::If {
                condition,
                then_branch: _,
                else_branch: _,
            },
            value,
        ) if computation_is_known_value(&value, context) => Some(is_bool(*condition)),
        _ => None,
    }
}

fn apply_value_argument(variable: Symbol, prop: Prop, context: &ProofContext) -> Option<Prop> {
    match prop {
        Prop::Equal(Computation::Apply { argument, .. }, value)
            if computation_is_known_value(&value, context) =>
        {
            Some(terminates(variable, *argument))
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValueConstructor {
    Symbol,
    Lambda,
    Bv32,
    Nil,
    Cons,
    List,
}

fn known_value_constructor(
    computation: &Computation,
    context: &ProofContext,
) -> Option<ValueConstructor> {
    if !computation_is_known_value(computation, context) {
        return None;
    }

    match computation {
        Computation::Quote(_) => Some(ValueConstructor::Symbol),
        Computation::Lambda(_) => Some(ValueConstructor::Lambda),
        Computation::Bv32(_) => Some(ValueConstructor::Bv32),
        Computation::Nil => Some(ValueConstructor::Nil),
        Computation::Cons { .. } => Some(ValueConstructor::Cons),
        Computation::Var(_) if computation_is_list(computation, context) => {
            Some(ValueConstructor::List)
        }
        _ => None,
    }
}

fn value_constructors_are_distinct(left: ValueConstructor, right: ValueConstructor) -> bool {
    use ValueConstructor::*;

    matches!(
        (left, right),
        (Symbol, Lambda | Bv32 | Nil | Cons | List)
            | (Lambda, Symbol | Bv32 | Nil | Cons | List)
            | (Bv32, Symbol | Lambda | Nil | Cons | List)
            | (Nil, Symbol | Lambda | Bv32 | Cons)
            | (Cons, Symbol | Lambda | Bv32 | Nil)
            | (List, Symbol | Lambda | Bv32)
    )
}

fn distinct_outcomes(prop: Prop, context: &ProofContext) -> Option<Prop> {
    match prop {
        Prop::Equal(left, right)
            if left
                .as_outcome()
                .zip(right.as_outcome())
                .is_some_and(|(left, right)| left != right) =>
        {
            Some(Prop::Absurd)
        }
        Prop::Equal(left, right)
            if known_value_constructor(&left, context)
                .zip(known_value_constructor(&right, context))
                .is_some_and(|(left, right)| value_constructors_are_distinct(left, right)) =>
        {
            Some(Prop::Absurd)
        }
        _ => None,
    }
}

fn value_non_symbol_non_lambda_non_bv32_is_list(
    value: Prop,
    not_symbol: Prop,
    not_lambda: Prop,
    not_bv32: Prop,
) -> Option<Prop> {
    let Prop::IsValue(computation) = value else {
        return None;
    };

    let expected_not_symbol = value_kind_is_not_kind(computation.clone(), SYMBOL_KIND_SYMBOL);
    let expected_not_lambda = value_kind_is_not_kind(computation.clone(), LAMBDA_KIND_SYMBOL);
    let expected_not_bv32 = value_kind_is_not_kind(computation.clone(), BV32_KIND_SYMBOL);

    if alpha_eq_prop(&not_symbol, &expected_not_symbol)
        && alpha_eq_prop(&not_lambda, &expected_not_lambda)
        && alpha_eq_prop(&not_bv32, &expected_not_bv32)
    {
        Some(Prop::IsList(computation))
    } else {
        None
    }
}

fn value_kind_is_not_kind(computation: Computation, kind: Symbol) -> Prop {
    equal(
        symbol_eq(value_kind(computation), Computation::Quote(kind)),
        Computation::Quote(FALSE_SYMBOL),
    )
}

fn value_kind_is_kind(computation: Computation, kind: Symbol) -> Prop {
    equal(
        symbol_eq(value_kind(computation), Computation::Quote(kind)),
        Computation::Quote(TRUE_SYMBOL),
    )
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ProofStepMode {
    Normal,
    Contextual,
}

fn step_for_proof(computation: &Computation, bindings: &Bindings, context: &ProofContext) -> Step {
    step_for_proof_with_mode(computation, bindings, context, ProofStepMode::Normal)
}

fn step_contextual_for_proof(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
) -> Step {
    step_for_proof_with_mode(computation, bindings, context, ProofStepMode::Contextual)
}

fn step_for_proof_with_mode(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    if mode == ProofStepMode::Contextual {
        if let Some(reduced) = context_reduction_for_proof(computation, bindings, context) {
            return Step::Reduced(reduced);
        }
    }

    match computation {
        Computation::Apply { function, argument } => {
            step_apply_for_proof(function, argument, bindings, context, mode)
        }
        Computation::Lambda(_) => Step::Normal,
        Computation::Nil => Step::Normal,
        Computation::Bv32(_) => Step::Normal,
        Computation::Cons { head, tail } => {
            step_cons_for_proof(head, tail, bindings, context, mode)
        }
        Computation::Head(computation) => step_head_for_proof(computation, bindings, context, mode),
        Computation::Tail(computation) => step_tail_for_proof(computation, bindings, context, mode),
        Computation::ListCase(list_case) => {
            step_list_case_for_proof(list_case, bindings, context, mode)
        }
        Computation::If {
            condition,
            then_branch,
            else_branch,
        } => step_if_for_proof(condition, then_branch, else_branch, bindings, context, mode),
        Computation::SymbolEq { left, right } => {
            step_symbol_eq_for_proof(left, right, bindings, context, mode)
        }
        Computation::Bv32Eq { left, right } => {
            step_bv32_binary_for_proof(Bv32BinaryOp::Eq, left, right, bindings, context, mode)
        }
        Computation::Bv32Add { left, right } => {
            step_bv32_binary_for_proof(Bv32BinaryOp::Add, left, right, bindings, context, mode)
        }
        Computation::Bv32Slt { left, right } => {
            step_bv32_binary_for_proof(Bv32BinaryOp::Slt, left, right, bindings, context, mode)
        }
        Computation::Bv32SignedAddOverflows { left, right } => step_bv32_binary_for_proof(
            Bv32BinaryOp::SignedAddOverflows,
            left,
            right,
            bindings,
            context,
            mode,
        ),
        Computation::ValueKind(computation) => {
            step_value_kind_for_proof(computation, bindings, context, mode)
        }
        Computation::Ref(name) => match bindings.computation(*name) {
            Some(computation) => Step::Reduced(computation.clone()),
            None => Step::Normal,
        },
        Computation::Error(_) | Computation::Diverge => Step::Normal,
        Computation::Var(_) | Computation::Quote(_) => Step::Normal,
    }
}

fn context_reduction_for_proof(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
) -> Option<Computation> {
    let mut assumptions = context.iter().collect::<Vec<_>>();
    assumptions.sort_by_key(|(symbol, _)| **symbol);

    for (_, prop) in assumptions {
        if let Some(reduced) =
            prop_context_reduction_for_proof(computation, prop, bindings, context)
        {
            return Some(reduced);
        }
    }

    None
}

fn prop_context_reduction_for_proof(
    computation: &Computation,
    prop: &Prop,
    bindings: &Bindings,
    context: &ProofContext,
) -> Option<Computation> {
    match prop {
        Prop::Equal(left, right)
            if !alpha_eq_computation(right, computation)
                && computation_is_context_reduction_target(right)
                && context_reduction_left_matches(left, computation, bindings, context) =>
        {
            Some(right.clone())
        }
        Prop::And(left, right) => {
            prop_context_reduction_for_proof(computation, left, bindings, context)
                .or_else(|| prop_context_reduction_for_proof(computation, right, bindings, context))
        }
        _ => None,
    }
}

fn context_reduction_left_matches(
    left: &Computation,
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
) -> bool {
    alpha_eq_computation(left, computation)
        || bounded_normal_forms_match_for_context_reduction(left, computation, bindings, context)
}

fn bounded_normal_forms_match_for_context_reduction(
    left: &Computation,
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
) -> bool {
    let Some(left_normal) = bounded_normal_form_for_context_reduction(left, bindings, context)
    else {
        return false;
    };
    let Some(computation_normal) =
        bounded_normal_form_for_context_reduction(computation, bindings, context)
    else {
        return false;
    };

    alpha_eq_computation(&left_normal, &computation_normal)
}

fn bounded_normal_form_for_context_reduction(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
) -> Option<Computation> {
    let mut computation = computation.clone();

    for _ in 0..128 {
        match step_for_proof_with_mode(&computation, bindings, context, ProofStepMode::Normal) {
            Step::Reduced(next) => computation = next,
            Step::Normal => return Some(computation),
        }
    }

    None
}

fn computation_is_context_reduction_target(computation: &Computation) -> bool {
    matches!(
        computation,
        Computation::Quote(TRUE_SYMBOL)
            | Computation::Quote(FALSE_SYMBOL)
            | Computation::Bv32(_)
            | Computation::Error(_)
            | Computation::Diverge
    )
}

fn step_apply_for_proof(
    function: &Computation,
    argument: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match function {
        Computation::Lambda(lambda) => {
            step_lambda_application_for_proof(lambda, argument, bindings, context, mode)
        }
        _ if computation_is_effect(function, context) => Step::Reduced(function.clone()),
        _ => match step_for_proof_with_mode(function, bindings, context, mode) {
            Step::Reduced(function) => Step::Reduced(Computation::Apply {
                function: Box::new(function),
                argument: Box::new(argument.clone()),
            }),
            Step::Normal if computation_is_known_non_callable(function, context) => {
                Step::Reduced(runtime_error())
            }
            Step::Normal => {
                step_neutral_application_for_proof(function, argument, bindings, context, mode)
            }
        },
    }
}

fn step_lambda_application_for_proof(
    lambda: &Lambda,
    argument: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(argument, bindings, context, mode) {
        Step::Reduced(argument) => Step::Reduced(Computation::Apply {
            function: Box::new(Computation::Lambda(lambda.clone())),
            argument: Box::new(argument),
        }),
        Step::Normal if computation_is_effect(argument, context) => Step::Reduced(argument.clone()),
        Step::Normal if computation_is_known_value(argument, context) => {
            Step::Reduced(substitute(lambda.body.as_ref(), lambda.parameter, argument))
        }
        Step::Normal => Step::Normal,
    }
}

fn step_neutral_application_for_proof(
    function: &Computation,
    argument: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(argument, bindings, context, mode) {
        Step::Reduced(argument) => Step::Reduced(Computation::Apply {
            function: Box::new(function.clone()),
            argument: Box::new(argument),
        }),
        Step::Normal if computation_is_effect(argument, context) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Normal,
    }
}

fn step_cons_for_proof(
    head: &Computation,
    tail: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(head, bindings, context, mode) {
        Step::Reduced(head) => Step::Reduced(Computation::Cons {
            head: Box::new(head),
            tail: Box::new(tail.clone()),
        }),
        Step::Normal if computation_is_effect(head, context) => Step::Reduced(head.clone()),
        Step::Normal => match step_for_proof_with_mode(tail, bindings, context, mode) {
            Step::Reduced(tail) => Step::Reduced(Computation::Cons {
                head: Box::new(head.clone()),
                tail: Box::new(tail),
            }),
            Step::Normal if computation_is_effect(tail, context) => Step::Reduced(tail.clone()),
            Step::Normal if computation_is_known_non_list(tail, context) => {
                Step::Reduced(runtime_error())
            }
            Step::Normal => Step::Normal,
        },
    }
}

fn step_head_for_proof(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(computation, bindings, context, mode) {
        Step::Reduced(computation) => Step::Reduced(Computation::Head(Box::new(computation))),
        Step::Normal if computation_is_effect(computation, context) => {
            Step::Reduced(computation.clone())
        }
        Step::Normal => match computation {
            Computation::Cons { head, .. } if computation_is_list(computation, context) => {
                Step::Reduced(head.as_ref().clone())
            }
            Computation::Nil
            | Computation::Quote(_)
            | Computation::Lambda(_)
            | Computation::Bv32(_) => Step::Reduced(runtime_error()),
            Computation::Ref(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_)
            | Computation::If { .. }
            | Computation::SymbolEq { .. }
            | Computation::Bv32Eq { .. }
            | Computation::Bv32Add { .. }
            | Computation::Bv32Slt { .. }
            | Computation::Bv32SignedAddOverflows { .. }
            | Computation::ValueKind(_)
            | Computation::Cons { .. }
            | Computation::Error(_)
            | Computation::Diverge => Step::Normal,
        },
    }
}

fn step_tail_for_proof(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(computation, bindings, context, mode) {
        Step::Reduced(computation) => Step::Reduced(Computation::Tail(Box::new(computation))),
        Step::Normal if computation_is_effect(computation, context) => {
            Step::Reduced(computation.clone())
        }
        Step::Normal => match computation {
            Computation::Cons { tail, .. } if computation_is_list(computation, context) => {
                Step::Reduced(tail.as_ref().clone())
            }
            Computation::Nil
            | Computation::Quote(_)
            | Computation::Lambda(_)
            | Computation::Bv32(_) => Step::Reduced(runtime_error()),
            Computation::Ref(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_)
            | Computation::If { .. }
            | Computation::SymbolEq { .. }
            | Computation::Bv32Eq { .. }
            | Computation::Bv32Add { .. }
            | Computation::Bv32Slt { .. }
            | Computation::Bv32SignedAddOverflows { .. }
            | Computation::ValueKind(_)
            | Computation::Cons { .. }
            | Computation::Error(_)
            | Computation::Diverge => Step::Normal,
        },
    }
}

fn step_list_case_for_proof(
    list_case: &ListCase,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(list_case.list.as_ref(), bindings, context, mode) {
        Step::Reduced(list) => Step::Reduced(Computation::ListCase(ListCase {
            list: Box::new(list),
            nil: list_case.nil.clone(),
            cons: list_case.cons,
            cons_case: list_case.cons_case.clone(),
        })),
        Step::Normal if computation_is_effect(list_case.list.as_ref(), context) => {
            Step::Reduced(list_case.list.as_ref().clone())
        }
        Step::Normal => match list_case.list.as_ref() {
            Computation::Nil => Step::Reduced(list_case.nil.as_ref().clone()),
            Computation::Cons { .. } if computation_is_list(list_case.list.as_ref(), context) => {
                Step::Reduced(substitute(
                    list_case.cons_case.as_ref(),
                    list_case.cons,
                    list_case.list.as_ref(),
                ))
            }
            _ if computation_is_known_non_list(list_case.list.as_ref(), context) => {
                Step::Reduced(runtime_error())
            }
            Computation::Quote(_) | Computation::Lambda(_) | Computation::Bv32(_) => Step::Normal,
            Computation::Ref(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_)
            | Computation::If { .. }
            | Computation::SymbolEq { .. }
            | Computation::Bv32Eq { .. }
            | Computation::Bv32Add { .. }
            | Computation::Bv32Slt { .. }
            | Computation::Bv32SignedAddOverflows { .. }
            | Computation::ValueKind(_)
            | Computation::Cons { .. }
            | Computation::Error(_)
            | Computation::Diverge => Step::Normal,
        },
    }
}

fn step_if_for_proof(
    condition: &Computation,
    then_branch: &Computation,
    else_branch: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(condition, bindings, context, mode) {
        Step::Reduced(condition) => Step::Reduced(Computation::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch.clone()),
            else_branch: Box::new(else_branch.clone()),
        }),
        Step::Normal if computation_is_effect(condition, context) => {
            Step::Reduced(condition.clone())
        }
        Step::Normal => match condition {
            Computation::Quote(TRUE_SYMBOL) => Step::Reduced(then_branch.clone()),
            Computation::Quote(FALSE_SYMBOL) => Step::Reduced(else_branch.clone()),
            _ if computation_is_known_non_bool(condition, context) => {
                Step::Reduced(runtime_error())
            }
            _ => Step::Normal,
        },
    }
}

fn step_symbol_eq_for_proof(
    left: &Computation,
    right: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(left, bindings, context, mode) {
        Step::Reduced(left) => Step::Reduced(Computation::SymbolEq {
            left: Box::new(left),
            right: Box::new(right.clone()),
        }),
        Step::Normal if computation_is_effect(left, context) => Step::Reduced(left.clone()),
        Step::Normal if !computation_is_known_value(left, context) => Step::Normal,
        Step::Normal => match step_for_proof_with_mode(right, bindings, context, mode) {
            Step::Reduced(right) => Step::Reduced(Computation::SymbolEq {
                left: Box::new(left.clone()),
                right: Box::new(right),
            }),
            Step::Normal if computation_is_effect(right, context) => Step::Reduced(right.clone()),
            Step::Normal if !computation_is_known_value(right, context) => Step::Normal,
            Step::Normal => {
                symbol_eq_result_for_proof(left, right, context).map_or(Step::Normal, Step::Reduced)
            }
        },
    }
}

fn symbol_eq_result_for_proof(
    left: &Computation,
    right: &Computation,
    context: &ProofContext,
) -> Option<Computation> {
    match (left, right) {
        _ if alpha_eq_computation(left, right)
            && computation_is_known_symbol_value(left, context) =>
        {
            Some(Computation::Quote(TRUE_SYMBOL))
        }
        (Computation::Quote(left), Computation::Quote(right)) if left == right => {
            Some(Computation::Quote(TRUE_SYMBOL))
        }
        (Computation::Quote(_), Computation::Quote(_)) => Some(Computation::Quote(FALSE_SYMBOL)),
        _ if computation_is_known_non_symbol_value(left, context)
            || computation_is_known_non_symbol_value(right, context) =>
        {
            Some(Computation::Quote(FALSE_SYMBOL))
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum Bv32BinaryOp {
    Eq,
    Add,
    Slt,
    SignedAddOverflows,
}

fn step_bv32_binary_for_proof(
    op: Bv32BinaryOp,
    left: &Computation,
    right: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(left, bindings, context, mode) {
        Step::Reduced(left) => Step::Reduced(rebuild_bv32_binary(op, left, right.clone())),
        Step::Normal if computation_is_effect(left, context) => Step::Reduced(left.clone()),
        Step::Normal if !computation_is_known_value(left, context) => Step::Normal,
        Step::Normal => match left {
            Computation::Bv32(left_value) => {
                match step_for_proof_with_mode(right, bindings, context, mode) {
                    Step::Reduced(right) => {
                        Step::Reduced(rebuild_bv32_binary(op, left.clone(), right))
                    }
                    Step::Normal if computation_is_effect(right, context) => {
                        Step::Reduced(right.clone())
                    }
                    Step::Normal if !computation_is_known_value(right, context) => Step::Normal,
                    Step::Normal => match right {
                        Computation::Bv32(right_value) => {
                            Step::Reduced(apply_bv32_binary(op, *left_value, *right_value))
                        }
                        _ => Step::Reduced(runtime_error()),
                    },
                }
            }
            _ => Step::Reduced(runtime_error()),
        },
    }
}

fn rebuild_bv32_binary(op: Bv32BinaryOp, left: Computation, right: Computation) -> Computation {
    match op {
        Bv32BinaryOp::Eq => Computation::Bv32Eq {
            left: Box::new(left),
            right: Box::new(right),
        },
        Bv32BinaryOp::Add => Computation::Bv32Add {
            left: Box::new(left),
            right: Box::new(right),
        },
        Bv32BinaryOp::Slt => Computation::Bv32Slt {
            left: Box::new(left),
            right: Box::new(right),
        },
        Bv32BinaryOp::SignedAddOverflows => Computation::Bv32SignedAddOverflows {
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}

fn apply_bv32_binary(op: Bv32BinaryOp, left: u32, right: u32) -> Computation {
    match op {
        Bv32BinaryOp::Eq => boolean_computation(left == right),
        Bv32BinaryOp::Add => Computation::Bv32(left.wrapping_add(right)),
        Bv32BinaryOp::Slt => boolean_computation((left as i32) < (right as i32)),
        Bv32BinaryOp::SignedAddOverflows => {
            boolean_computation((left as i32).overflowing_add(right as i32).1)
        }
    }
}

fn boolean_computation(value: bool) -> Computation {
    Computation::Quote(if value { TRUE_SYMBOL } else { FALSE_SYMBOL })
}

fn step_value_kind_for_proof(
    computation: &Computation,
    bindings: &Bindings,
    context: &ProofContext,
    mode: ProofStepMode,
) -> Step {
    match step_for_proof_with_mode(computation, bindings, context, mode) {
        Step::Reduced(computation) => Step::Reduced(Computation::ValueKind(Box::new(computation))),
        Step::Normal if computation_is_effect(computation, context) => {
            Step::Reduced(computation.clone())
        }
        Step::Normal => {
            value_kind_result_for_proof(computation, context).map_or(Step::Normal, Step::Reduced)
        }
    }
}

fn value_kind_result_for_proof(
    computation: &Computation,
    context: &ProofContext,
) -> Option<Computation> {
    for kind in [
        SYMBOL_KIND_SYMBOL,
        LAMBDA_KIND_SYMBOL,
        BV32_KIND_SYMBOL,
        LIST_KIND_SYMBOL,
    ] {
        if context_contains_prop(context, &value_kind_is_kind(computation.clone(), kind)) {
            return Some(Computation::Quote(kind));
        }
    }

    match computation {
        Computation::Quote(_) => Some(Computation::Quote(SYMBOL_KIND_SYMBOL)),
        Computation::Lambda(_) => Some(Computation::Quote(LAMBDA_KIND_SYMBOL)),
        Computation::Bv32(_) => Some(Computation::Quote(BV32_KIND_SYMBOL)),
        _ if computation_is_list(computation, context) => {
            Some(Computation::Quote(LIST_KIND_SYMBOL))
        }
        _ => None,
    }
}

fn runtime_error() -> Computation {
    Computation::Error(RUNTIME_ERROR)
}

fn computation_is_known_non_callable(computation: &Computation, context: &ProofContext) -> bool {
    match computation {
        Computation::Quote(_) | Computation::Nil | Computation::Bv32(_) => true,
        Computation::Cons { .. } => computation_is_list(computation, context),
        Computation::Var(_) => computation_is_list(computation, context),
        _ => false,
    }
}

fn computation_is_known_non_list(computation: &Computation, context: &ProofContext) -> bool {
    matches!(
        computation,
        Computation::Quote(_) | Computation::Lambda(_) | Computation::Bv32(_)
    ) || context_contains_prop(
        context,
        &value_kind_is_kind(computation.clone(), SYMBOL_KIND_SYMBOL),
    ) || context_contains_prop(
        context,
        &value_kind_is_kind(computation.clone(), LAMBDA_KIND_SYMBOL),
    ) || context_contains_prop(
        context,
        &value_kind_is_kind(computation.clone(), BV32_KIND_SYMBOL),
    )
}

fn computation_is_known_non_bool(computation: &Computation, context: &ProofContext) -> bool {
    match computation {
        Computation::Quote(symbol) => !matches!(*symbol, TRUE_SYMBOL | FALSE_SYMBOL),
        Computation::Nil | Computation::Lambda(_) | Computation::Bv32(_) => true,
        Computation::Cons { .. } | Computation::Var(_) => computation_is_list(computation, context),
        _ => false,
    }
}

fn computation_is_known_non_symbol_value(
    computation: &Computation,
    context: &ProofContext,
) -> bool {
    match computation {
        Computation::Nil | Computation::Lambda(_) | Computation::Bv32(_) => true,
        Computation::Cons { .. } => computation_is_list(computation, context),
        Computation::Var(_) => computation_is_list(computation, context),
        _ => false,
    }
}

fn computation_is_known_symbol_value(computation: &Computation, context: &ProofContext) -> bool {
    matches!(computation, Computation::Quote(_))
        || context_contains_prop(
            context,
            &value_kind_is_kind(computation.clone(), SYMBOL_KIND_SYMBOL),
        )
}

fn proven_steps(
    computations: &[Computation],
    bindings: &Bindings,
    context: &ProofContext,
) -> Option<Prop> {
    let (first, rest) = computations.split_first()?;
    let mut previous = first;

    for next in rest {
        match step_for_proof(previous, bindings, context) {
            Step::Reduced(reduced) if alpha_eq_computation(&reduced, next) => previous = next,
            _ => return None,
        }
    }

    Some(Prop::Equal(first.clone(), previous.clone()))
}

fn proven_context_steps(
    computations: &[Computation],
    bindings: &Bindings,
    context: &ProofContext,
) -> Option<Prop> {
    let (first, rest) = computations.split_first()?;
    let mut previous = first;

    for next in rest {
        match step_contextual_for_proof(previous, bindings, context) {
            Step::Reduced(reduced) if alpha_eq_computation(&reduced, next) => previous = next,
            _ => return None,
        }
    }

    Some(Prop::Equal(first.clone(), previous.clone()))
}

#[derive(Clone, Copy)]
struct ListInductionSymbols {
    variable: Symbol,
    head: Symbol,
    tail: Symbol,
    induction_hypothesis_assumption: Symbol,
}

#[derive(Clone, Copy)]
struct ValueInductionSymbols {
    variable: Symbol,
    symbol_assumption: Symbol,
    lambda_assumption: Symbol,
    bv32_assumption: Symbol,
    head: Symbol,
    tail: Symbol,
    head_induction_hypothesis_assumption: Symbol,
    tail_induction_hypothesis_assumption: Symbol,
}

struct ValueInductionCases<'a> {
    symbol_case: &'a Proof,
    lambda_case: &'a Proof,
    bv32_case: &'a Proof,
    nil_case: &'a Proof,
    cons_case: &'a Proof,
}

fn prove_list_induction(
    bindings: &Bindings,
    context: &ProofContext,
    symbols: ListInductionSymbols,
    property: &Prop,
    base: &Proof,
    step: &Proof,
) -> Option<Prop> {
    if !list_induction_symbols_are_fresh(context, symbols, property) {
        return None;
    }

    let ListInductionSymbols {
        variable,
        head,
        tail,
        induction_hypothesis_assumption,
    } = symbols;

    let base_prop = substitute_prop(property, variable, &Computation::Nil);
    if !alpha_eq_prop(
        &proven_prop_in_context(base, bindings, context)?,
        &base_prop,
    ) {
        return None;
    }

    let tail_var = Computation::Var(tail);
    let step_prop = substitute_prop(
        property,
        variable,
        &Computation::Cons {
            head: Box::new(Computation::Var(head)),
            tail: Box::new(tail_var.clone()),
        },
    );
    let mut step_context = context.clone();
    step_context.insert(
        induction_hypothesis_assumption,
        substitute_prop(property, variable, &tail_var),
    );
    step_context.insert(head, is_value(Computation::Var(head)));
    step_context.insert(tail, is_list(Computation::Var(tail)));

    if !alpha_eq_prop(
        &proven_prop_in_context(step, bindings, &step_context)?,
        &step_prop,
    ) {
        return None;
    }

    let variable_computation = Computation::Var(variable);
    Some(forall_where(
        variable,
        is_list(variable_computation.clone()),
        substitute_prop(property, variable, &variable_computation),
    ))
}

fn prove_value_induction(
    bindings: &Bindings,
    context: &ProofContext,
    symbols: ValueInductionSymbols,
    property: &Prop,
    cases: ValueInductionCases<'_>,
) -> Option<Prop> {
    if !value_induction_symbols_are_fresh(context, symbols, property) {
        return None;
    }

    let ValueInductionSymbols {
        variable,
        symbol_assumption,
        lambda_assumption,
        bv32_assumption,
        head,
        tail,
        head_induction_hypothesis_assumption,
        tail_induction_hypothesis_assumption,
    } = symbols;

    let variable_computation = Computation::Var(variable);
    let variable_prop = substitute_prop(property, variable, &variable_computation);

    let mut symbol_context = context.clone();
    symbol_context.insert(variable, is_value(variable_computation.clone()));
    symbol_context.insert(
        symbol_assumption,
        value_kind_is_kind(variable_computation.clone(), SYMBOL_KIND_SYMBOL),
    );
    if !alpha_eq_prop(
        &proven_prop_in_context(cases.symbol_case, bindings, &symbol_context)?,
        &variable_prop,
    ) {
        return None;
    }

    let mut lambda_context = context.clone();
    lambda_context.insert(variable, is_value(variable_computation.clone()));
    lambda_context.insert(
        lambda_assumption,
        value_kind_is_kind(variable_computation.clone(), LAMBDA_KIND_SYMBOL),
    );
    if !alpha_eq_prop(
        &proven_prop_in_context(cases.lambda_case, bindings, &lambda_context)?,
        &variable_prop,
    ) {
        return None;
    }

    let mut bv32_context = context.clone();
    bv32_context.insert(variable, is_value(variable_computation.clone()));
    bv32_context.insert(
        bv32_assumption,
        value_kind_is_kind(variable_computation.clone(), BV32_KIND_SYMBOL),
    );
    if !alpha_eq_prop(
        &proven_prop_in_context(cases.bv32_case, bindings, &bv32_context)?,
        &variable_prop,
    ) {
        return None;
    }

    let nil_prop = substitute_prop(property, variable, &Computation::Nil);
    if !alpha_eq_prop(
        &proven_prop_in_context(cases.nil_case, bindings, context)?,
        &nil_prop,
    ) {
        return None;
    }

    let head_var = Computation::Var(head);
    let tail_var = Computation::Var(tail);
    let cons = Computation::Cons {
        head: Box::new(head_var.clone()),
        tail: Box::new(tail_var.clone()),
    };
    let cons_prop = substitute_prop(property, variable, &cons);
    let mut cons_context = context.clone();
    cons_context.insert(head, is_value(head_var.clone()));
    cons_context.insert(tail, is_list(tail_var.clone()));
    cons_context.insert(
        head_induction_hypothesis_assumption,
        substitute_prop(property, variable, &head_var),
    );
    cons_context.insert(
        tail_induction_hypothesis_assumption,
        substitute_prop(property, variable, &tail_var),
    );
    if !alpha_eq_prop(
        &proven_prop_in_context(cases.cons_case, bindings, &cons_context)?,
        &cons_prop,
    ) {
        return None;
    }

    Some(forall_where(
        variable,
        is_value(variable_computation.clone()),
        variable_prop,
    ))
}

fn list_induction_symbols_are_fresh(
    context: &ProofContext,
    symbols: ListInductionSymbols,
    property: &Prop,
) -> bool {
    let ListInductionSymbols {
        variable,
        head,
        tail,
        induction_hypothesis_assumption,
    } = symbols;

    if head == tail || head == variable || tail == variable {
        return false;
    }

    let assumption_symbols = [induction_hypothesis_assumption];
    let mut seen_assumption_symbols = HashSet::new();
    if assumption_symbols
        .into_iter()
        .chain([head, tail])
        .any(|assumption| {
            !seen_assumption_symbols.insert(assumption) || context.contains_key(&assumption)
        })
    {
        return false;
    }

    !context_mentions_symbol(context, variable)
        && !context_mentions_symbol(context, head)
        && !context_mentions_symbol(context, tail)
        && !prop_mentions_symbol(property, head)
        && !prop_mentions_symbol(property, tail)
}

fn value_induction_symbols_are_fresh(
    context: &ProofContext,
    symbols: ValueInductionSymbols,
    property: &Prop,
) -> bool {
    let ValueInductionSymbols {
        variable,
        symbol_assumption,
        lambda_assumption,
        bv32_assumption,
        head,
        tail,
        head_induction_hypothesis_assumption,
        tail_induction_hypothesis_assumption,
    } = symbols;

    let symbols = [
        variable,
        symbol_assumption,
        lambda_assumption,
        bv32_assumption,
        head,
        tail,
        head_induction_hypothesis_assumption,
        tail_induction_hypothesis_assumption,
    ];
    let mut seen_symbols = HashSet::new();
    if symbols
        .into_iter()
        .any(|symbol| !seen_symbols.insert(symbol) || context.contains_key(&symbol))
    {
        return false;
    }

    !context_mentions_symbol(context, variable)
        && !context_mentions_symbol(context, symbol_assumption)
        && !context_mentions_symbol(context, lambda_assumption)
        && !context_mentions_symbol(context, bv32_assumption)
        && !context_mentions_symbol(context, head)
        && !context_mentions_symbol(context, tail)
        && !context_mentions_symbol(context, head_induction_hypothesis_assumption)
        && !context_mentions_symbol(context, tail_induction_hypothesis_assumption)
        && !prop_mentions_symbol(property, symbol_assumption)
        && !prop_mentions_symbol(property, lambda_assumption)
        && !prop_mentions_symbol(property, bv32_assumption)
        && !prop_mentions_symbol(property, head)
        && !prop_mentions_symbol(property, tail)
        && !prop_mentions_symbol(property, head_induction_hypothesis_assumption)
        && !prop_mentions_symbol(property, tail_induction_hypothesis_assumption)
}

fn computation_is_list(computation: &Computation, context: &ProofContext) -> bool {
    if context_contains_prop(context, &is_list(computation.clone())) {
        return true;
    }

    match computation {
        Computation::Nil => true,
        Computation::Cons { head, tail } => {
            computation_is_known_value(head, context) && computation_is_list(tail, context)
        }
        _ => false,
    }
}

fn computation_is_known_value(computation: &Computation, context: &ProofContext) -> bool {
    if context_contains_prop(context, &is_value(computation.clone()))
        || computation.as_value().is_some()
        || computation_is_list(computation, context)
        || context_contains_prop(
            context,
            &value_kind_is_kind(computation.clone(), SYMBOL_KIND_SYMBOL),
        )
        || context_contains_prop(
            context,
            &value_kind_is_kind(computation.clone(), LAMBDA_KIND_SYMBOL),
        )
        || context_contains_prop(
            context,
            &value_kind_is_kind(computation.clone(), LIST_KIND_SYMBOL),
        )
        || context_contains_prop(
            context,
            &value_kind_is_kind(computation.clone(), BV32_KIND_SYMBOL),
        )
    {
        return true;
    }

    false
}

fn computation_is_effect(computation: &Computation, context: &ProofContext) -> bool {
    context_contains_prop(context, &is_effect(computation.clone()))
        || computation.as_effect().is_some()
}

fn computation_is_outcome(computation: &Computation, context: &ProofContext) -> bool {
    context_contains_prop(context, &is_outcome(computation.clone()))
        || computation_is_known_value(computation, context)
        || computation_is_effect(computation, context)
}

pub(crate) fn primitive_prop_holds(prop: &Prop, context: &ProofContext) -> bool {
    structural_primitive_prop_holds(prop, context) || context_contains_prop(context, prop)
}

pub(crate) fn structural_primitive_prop_holds(prop: &Prop, context: &ProofContext) -> bool {
    match prop {
        Prop::IsValue(computation) => computation_is_known_value(computation, context),
        Prop::IsList(computation) => computation_is_list(computation, context),
        Prop::IsEffect(computation) => computation_is_effect(computation, context),
        Prop::IsOutcome(computation) => computation_is_outcome(computation, context),
        _ => false,
    }
}

fn context_contains_prop(context: &ProofContext, target: &Prop) -> bool {
    context
        .values()
        .any(|prop| prop_contains_prop(prop, target))
}

fn prop_contains_prop(prop: &Prop, target: &Prop) -> bool {
    alpha_eq_prop(prop, target)
        || match prop {
            Prop::And(left, right) => {
                prop_contains_prop(left, target) || prop_contains_prop(right, target)
            }
            _ => false,
        }
}

pub fn substitute_prop(prop: &Prop, variable: Symbol, replacement: &Computation) -> Prop {
    match prop {
        Prop::Absurd => Prop::Absurd,
        Prop::Equal(left, right) => Prop::Equal(
            substitute(left, variable, replacement),
            substitute(right, variable, replacement),
        ),
        Prop::IsValue(computation) => Prop::IsValue(substitute(computation, variable, replacement)),
        Prop::IsList(computation) => Prop::IsList(substitute(computation, variable, replacement)),
        Prop::IsEffect(computation) => {
            Prop::IsEffect(substitute(computation, variable, replacement))
        }
        Prop::IsOutcome(computation) => {
            Prop::IsOutcome(substitute(computation, variable, replacement))
        }
        Prop::Implies(premise, conclusion) => Prop::Implies(
            Box::new(substitute_prop(premise, variable, replacement)),
            Box::new(substitute_prop(conclusion, variable, replacement)),
        ),
        Prop::ForAll {
            variable: binder,
            body,
        } => substitute_quantified_prop(Quantifier::ForAll, *binder, body, variable, replacement),
        Prop::Exists {
            variable: binder,
            body,
        } => substitute_quantified_prop(Quantifier::Exists, *binder, body, variable, replacement),
        Prop::And(left, right) => Prop::And(
            Box::new(substitute_prop(left, variable, replacement)),
            Box::new(substitute_prop(right, variable, replacement)),
        ),
        Prop::Or(left, right) => Prop::Or(
            Box::new(substitute_prop(left, variable, replacement)),
            Box::new(substitute_prop(right, variable, replacement)),
        ),
    }
}

#[derive(Clone, Copy)]
enum Quantifier {
    ForAll,
    Exists,
}

fn substitute_quantified_prop(
    quantifier: Quantifier,
    binder: Symbol,
    body: &Prop,
    variable: Symbol,
    replacement: &Computation,
) -> Prop {
    if binder == variable {
        return quantified_prop(quantifier, binder, body.clone());
    }

    if free_symbols(replacement).contains(&binder) {
        let fresh = fresh_symbol_for_quantified_prop(body, replacement, variable);
        let body = rename_bound_var_prop(body, binder, fresh);
        return quantified_prop(
            quantifier,
            fresh,
            substitute_prop(&body, variable, replacement),
        );
    }

    quantified_prop(
        quantifier,
        binder,
        substitute_prop(body, variable, replacement),
    )
}

fn quantified_prop(quantifier: Quantifier, variable: Symbol, body: Prop) -> Prop {
    match quantifier {
        Quantifier::ForAll => Prop::ForAll {
            variable,
            body: Box::new(body),
        },
        Quantifier::Exists => Prop::Exists {
            variable,
            body: Box::new(body),
        },
    }
}

pub fn free_symbols_prop(prop: &Prop) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols_prop(prop, &mut symbols);
    symbols
}

fn add_free_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Absurd => {}
        Prop::Equal(left, right) => {
            add_free_symbols(left, symbols);
            add_free_symbols(right, symbols);
        }
        Prop::IsValue(computation)
        | Prop::IsList(computation)
        | Prop::IsEffect(computation)
        | Prop::IsOutcome(computation) => {
            add_free_symbols(computation, symbols);
        }
        Prop::Implies(premise, conclusion)
        | Prop::And(premise, conclusion)
        | Prop::Or(premise, conclusion) => {
            add_free_symbols_prop(premise, symbols);
            add_free_symbols_prop(conclusion, symbols);
        }
        Prop::ForAll { variable, body } | Prop::Exists { variable, body } => {
            let mut body_symbols = HashSet::new();
            add_free_symbols_prop(body, &mut body_symbols);
            body_symbols.remove(variable);
            symbols.extend(body_symbols);
        }
    }
}

fn rename_bound_var_prop(prop: &Prop, old: Symbol, new: Symbol) -> Prop {
    match prop {
        Prop::Absurd => Prop::Absurd,
        Prop::Equal(left, right) => Prop::Equal(
            rename_bound_var(left, old, new),
            rename_bound_var(right, old, new),
        ),
        Prop::IsValue(computation) => Prop::IsValue(rename_bound_var(computation, old, new)),
        Prop::IsList(computation) => Prop::IsList(rename_bound_var(computation, old, new)),
        Prop::IsEffect(computation) => Prop::IsEffect(rename_bound_var(computation, old, new)),
        Prop::IsOutcome(computation) => Prop::IsOutcome(rename_bound_var(computation, old, new)),
        Prop::Implies(premise, conclusion) => Prop::Implies(
            Box::new(rename_bound_var_prop(premise, old, new)),
            Box::new(rename_bound_var_prop(conclusion, old, new)),
        ),
        Prop::ForAll { variable, .. } if *variable == old => prop.clone(),
        Prop::ForAll { variable, body } => Prop::ForAll {
            variable: *variable,
            body: Box::new(rename_bound_var_prop(body, old, new)),
        },
        Prop::Exists { variable, .. } if *variable == old => prop.clone(),
        Prop::Exists { variable, body } => Prop::Exists {
            variable: *variable,
            body: Box::new(rename_bound_var_prop(body, old, new)),
        },
        Prop::And(left, right) => Prop::And(
            Box::new(rename_bound_var_prop(left, old, new)),
            Box::new(rename_bound_var_prop(right, old, new)),
        ),
        Prop::Or(left, right) => Prop::Or(
            Box::new(rename_bound_var_prop(left, old, new)),
            Box::new(rename_bound_var_prop(right, old, new)),
        ),
    }
}

fn fresh_symbol_for_quantified_prop(
    body: &Prop,
    replacement: &Computation,
    variable: Symbol,
) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols_prop(body, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    fresh_symbol_avoiding(&symbols)
}

fn fresh_symbol_avoiding(symbols: &HashSet<Symbol>) -> Symbol {
    let mut symbol = Symbol(0);
    while symbols.contains(&symbol) {
        symbol = Symbol(symbol.0 + 1);
    }
    symbol
}

fn add_all_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Absurd => {}
        Prop::Equal(left, right) => {
            add_all_symbols(left, symbols);
            add_all_symbols(right, symbols);
        }
        Prop::IsValue(computation)
        | Prop::IsList(computation)
        | Prop::IsEffect(computation)
        | Prop::IsOutcome(computation) => {
            add_all_symbols(computation, symbols);
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

fn prop_mentions_symbol(prop: &Prop, symbol: Symbol) -> bool {
    free_symbols_prop(prop).contains(&symbol)
}

fn context_mentions_symbol(context: &ProofContext, symbol: Symbol) -> bool {
    context
        .values()
        .any(|prop| prop_mentions_symbol(prop, symbol))
}
