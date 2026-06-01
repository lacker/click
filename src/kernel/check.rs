use std::collections::HashSet;

use super::{
    calculus::*,
    eval::{argument_is_ready_for_beta, step_in_bindings},
    theory::{Bindings, Context},
};

pub fn check(proof: &Proof, prop: &Prop) -> bool {
    check_in_context(proof, prop, &Context::new())
}

pub fn check_in_context(proof: &Proof, prop: &Prop, context: &Context) -> bool {
    check_in_bindings_and_context(proof, prop, &Bindings::new(), context)
}

pub(crate) fn check_in_bindings(proof: &Proof, prop: &Prop, bindings: &Bindings) -> bool {
    check_in_bindings_and_context(proof, prop, bindings, &Context::new())
}

pub(super) fn check_in_bindings_and_context(
    proof: &Proof,
    prop: &Prop,
    bindings: &Bindings,
    context: &Context,
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
        (Prop::Equal(left_left, left_right), Prop::Equal(right_left, right_right)) => {
            alpha_eq_computation_in_context(left_left, right_left, bindings)
                && alpha_eq_computation_in_context(left_right, right_right, bindings)
        }
        (Prop::IsValue(left), Prop::IsValue(right)) => {
            alpha_eq_computation_in_context(left, right, bindings)
        }
        (Prop::IsList(left), Prop::IsList(right)) => {
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
        (Computation::Const(left), Computation::Const(right)) => left == right,
        (Computation::Error(left), Computation::Error(right)) => {
            alpha_eq_computation_in_context(left, right, bindings)
        }
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

pub(super) fn proven_prop(proof: &Proof, bindings: &Bindings, context: &Context) -> Option<Prop> {
    match proof {
        Proof::Known(name) => bindings.theorem(*name).cloned(),
        Proof::Assume(symbol) => context.get(symbol).cloned(),
        Proof::Refl(computation) => Some(Prop::Equal(computation.clone(), computation.clone())),
        Proof::Symm(proof) => match proven_prop(proof, bindings, context)? {
            Prop::Equal(left, right) => Some(Prop::Equal(right, left)),
            _ => None,
        },
        Proof::Trans(first, second) => {
            match (
                proven_prop(first, bindings, context)?,
                proven_prop(second, bindings, context)?,
            ) {
                (Prop::Equal(left, middle), Prop::Equal(second_middle, right))
                    if alpha_eq_computation(&middle, &second_middle) =>
                {
                    Some(Prop::Equal(left, right))
                }
                _ => None,
            }
        }
        Proof::Step(computation) => match step_in_bindings(computation, bindings) {
            Step::Reduced(reduced) => Some(Prop::Equal(computation.clone(), reduced)),
            Step::Normal => None,
        },
        Proof::Steps(computations) => proven_steps(computations, bindings),
        Proof::Rewrite {
            equality,
            proof,
            variable,
            template,
        } => {
            let Prop::Equal(left, right) = proven_prop(equality, bindings, context)? else {
                return None;
            };

            let left_instance = substitute_prop(template, *variable, &left);
            if !alpha_eq_prop(&proven_prop(proof, bindings, context)?, &left_instance) {
                return None;
            }

            Some(substitute_prop(template, *variable, &right))
        }
        Proof::Beta { lambda, argument } => {
            if !argument_is_ready_for_beta(argument, bindings) {
                return None;
            }

            let applied = Computation::Apply {
                function: Box::new(Computation::Lambda(lambda.clone())),
                argument: Box::new(argument.clone()),
            };
            let reduced = substitute(lambda.body.as_ref(), lambda.parameter, argument);
            Some(Prop::Equal(applied, reduced))
        }
        Proof::Value(value) => Some(Prop::IsValue(value.clone().into_computation())),
        Proof::ValueCons {
            head,
            tail,
            head_is_value,
            tail_is_value,
        } => match (
            proven_prop(head_is_value, bindings, context)?,
            proven_prop(tail_is_value, bindings, context)?,
        ) {
            (Prop::IsValue(proven_head), Prop::IsValue(proven_tail))
                if alpha_eq_computation(&proven_head, head)
                    && alpha_eq_computation(&proven_tail, tail) =>
            {
                Some(Prop::IsValue(Computation::Cons {
                    head: Box::new(head.clone()),
                    tail: Box::new(tail.clone()),
                }))
            }
            _ => None,
        },
        Proof::ListNil => Some(Prop::IsList(Computation::Nil)),
        Proof::ListCons {
            head,
            tail,
            head_is_value,
            tail_is_list,
        } => match (
            proven_prop(head_is_value, bindings, context)?,
            proven_prop(tail_is_list, bindings, context)?,
        ) {
            (Prop::IsValue(proven_head), Prop::IsList(proven_tail))
                if alpha_eq_computation(&proven_head, head)
                    && alpha_eq_computation(&proven_tail, tail) =>
            {
                Some(Prop::IsList(Computation::Cons {
                    head: Box::new(head.clone()),
                    tail: Box::new(tail.clone()),
                }))
            }
            _ => None,
        },
        Proof::ListInduction {
            variable,
            property,
            base,
            head,
            tail,
            head_is_value_assumption,
            tail_is_list_assumption,
            induction_hypothesis_assumption,
            step,
        } => {
            let symbols = ListInductionSymbols {
                variable: *variable,
                head: *head,
                tail: *tail,
                head_is_value_assumption: *head_is_value_assumption,
                tail_is_list_assumption: *tail_is_list_assumption,
                induction_hypothesis_assumption: *induction_hypothesis_assumption,
            };

            prove_list_induction(bindings, context, symbols, property, base, step)
        }
        Proof::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => {
            let mut context = context.clone();
            context.insert(*assumption, premise.clone());
            let conclusion = proven_prop(proof, bindings, &context)?;
            Some(Prop::Implies(
                Box::new(premise.clone()),
                Box::new(conclusion),
            ))
        }
        Proof::ImpliesElim {
            implication,
            premise,
        } => {
            let premise = proven_prop(premise, bindings, context)?;
            match proven_prop(implication, bindings, context)? {
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
            let body = proven_prop(proof, bindings, context)?;
            Some(Prop::ForAll {
                variable: *variable,
                body: Box::new(body),
            })
        }
        Proof::ForAllElim { forall, argument } => match proven_prop(forall, bindings, context)? {
            Prop::ForAll { variable, body } => Some(substitute_prop(&body, variable, argument)),
            _ => None,
        },
        Proof::ExistsIntro {
            variable,
            body,
            witness,
            proof,
        } => {
            let witness_body = substitute_prop(body, *variable, witness);
            if alpha_eq_prop(&proven_prop(proof, bindings, context)?, &witness_body) {
                Some(Prop::Exists {
                    variable: *variable,
                    body: Box::new(body.clone()),
                })
            } else {
                None
            }
        }
        Proof::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        } => match proven_prop(existential, bindings, context)? {
            Prop::Exists { variable, body } => {
                let existential = Prop::Exists {
                    variable,
                    body: body.clone(),
                };
                if prop_mentions_symbol(&existential, *witness)
                    || context_mentions_symbol(context, *witness)
                {
                    return None;
                }

                let witness_prop = substitute_prop(&body, variable, &Computation::Var(*witness));
                let mut context = context.clone();
                context.insert(*assumption, witness_prop);
                let conclusion = proven_prop(proof, bindings, &context)?;

                if prop_mentions_symbol(&conclusion, *witness) {
                    None
                } else {
                    Some(conclusion)
                }
            }
            _ => None,
        },
        Proof::AndIntro(left, right) => Some(Prop::And(
            Box::new(proven_prop(left, bindings, context)?),
            Box::new(proven_prop(right, bindings, context)?),
        )),
        Proof::AndElimLeft(proof) => match proven_prop(proof, bindings, context)? {
            Prop::And(left, _) => Some(*left),
            _ => None,
        },
        Proof::AndElimRight(proof) => match proven_prop(proof, bindings, context)? {
            Prop::And(_, right) => Some(*right),
            _ => None,
        },
        Proof::OrIntroLeft { proof, right } => Some(Prop::Or(
            Box::new(proven_prop(proof, bindings, context)?),
            Box::new(right.clone()),
        )),
        Proof::OrIntroRight { left, proof } => Some(Prop::Or(
            Box::new(left.clone()),
            Box::new(proven_prop(proof, bindings, context)?),
        )),
        Proof::OrElim {
            disjunction,
            left_assumption,
            left_proof,
            right_assumption,
            right_proof,
        } => match proven_prop(disjunction, bindings, context)? {
            Prop::Or(left, right) => {
                let mut left_context = context.clone();
                left_context.insert(*left_assumption, *left);
                let left_conclusion = proven_prop(left_proof, bindings, &left_context)?;

                let mut right_context = context.clone();
                right_context.insert(*right_assumption, *right);
                let right_conclusion = proven_prop(right_proof, bindings, &right_context)?;

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

fn proven_steps(computations: &[Computation], bindings: &Bindings) -> Option<Prop> {
    let (first, rest) = computations.split_first()?;
    let mut previous = first;

    for next in rest {
        match step_in_bindings(previous, bindings) {
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
    head_is_value_assumption: Symbol,
    tail_is_list_assumption: Symbol,
    induction_hypothesis_assumption: Symbol,
}

fn prove_list_induction(
    bindings: &Bindings,
    context: &Context,
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
        head_is_value_assumption,
        tail_is_list_assumption,
        induction_hypothesis_assumption,
    } = symbols;

    let base_prop = substitute_prop(property, variable, &Computation::Nil);
    if !alpha_eq_prop(&proven_prop(base, bindings, context)?, &base_prop) {
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
        head_is_value_assumption,
        Prop::IsValue(Computation::Var(head)),
    );
    step_context.insert(tail_is_list_assumption, Prop::IsList(tail_var.clone()));
    step_context.insert(
        induction_hypothesis_assumption,
        substitute_prop(property, variable, &tail_var),
    );

    if !alpha_eq_prop(&proven_prop(step, bindings, &step_context)?, &step_prop) {
        return None;
    }

    let variable_computation = Computation::Var(variable);
    Some(Prop::ForAll {
        variable,
        body: Box::new(Prop::Implies(
            Box::new(Prop::IsList(variable_computation.clone())),
            Box::new(substitute_prop(property, variable, &variable_computation)),
        )),
    })
}

fn list_induction_symbols_are_fresh(
    context: &Context,
    symbols: ListInductionSymbols,
    property: &Prop,
) -> bool {
    let ListInductionSymbols {
        variable,
        head,
        tail,
        head_is_value_assumption,
        tail_is_list_assumption,
        induction_hypothesis_assumption,
    } = symbols;

    if head == tail || head == variable || tail == variable {
        return false;
    }

    let assumption_symbols = [
        head_is_value_assumption,
        tail_is_list_assumption,
        induction_hypothesis_assumption,
    ];
    let mut seen_assumption_symbols = HashSet::new();
    if assumption_symbols.into_iter().any(|assumption| {
        !seen_assumption_symbols.insert(assumption) || context.contains_key(&assumption)
    }) {
        return false;
    }

    !context_mentions_symbol(context, variable)
        && !context_mentions_symbol(context, head)
        && !context_mentions_symbol(context, tail)
        && !prop_mentions_symbol(property, head)
        && !prop_mentions_symbol(property, tail)
}

pub fn substitute_prop(prop: &Prop, variable: Symbol, replacement: &Computation) -> Prop {
    match prop {
        Prop::Equal(left, right) => Prop::Equal(
            substitute(left, variable, replacement),
            substitute(right, variable, replacement),
        ),
        Prop::IsValue(computation) => Prop::IsValue(substitute(computation, variable, replacement)),
        Prop::IsList(computation) => Prop::IsList(substitute(computation, variable, replacement)),
        Prop::Implies(premise, conclusion) => Prop::Implies(
            Box::new(substitute_prop(premise, variable, replacement)),
            Box::new(substitute_prop(conclusion, variable, replacement)),
        ),
        Prop::ForAll {
            variable: binder,
            body,
        } => substitute_quantified_prop(true, *binder, body, variable, replacement),
        Prop::Exists {
            variable: binder,
            body,
        } => substitute_quantified_prop(false, *binder, body, variable, replacement),
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

fn substitute_quantified_prop(
    forall: bool,
    binder: Symbol,
    body: &Prop,
    variable: Symbol,
    replacement: &Computation,
) -> Prop {
    if binder == variable {
        return quantified_prop(forall, binder, body.clone());
    }

    if free_symbols(replacement).contains(&binder) {
        let fresh = fresh_symbol_for_prop(body, replacement, variable);
        let body = rename_bound_var_prop(body, binder, fresh);
        return quantified_prop(forall, fresh, substitute_prop(&body, variable, replacement));
    }

    quantified_prop(forall, binder, substitute_prop(body, variable, replacement))
}

fn quantified_prop(forall: bool, variable: Symbol, body: Prop) -> Prop {
    if forall {
        Prop::ForAll {
            variable,
            body: Box::new(body),
        }
    } else {
        Prop::Exists {
            variable,
            body: Box::new(body),
        }
    }
}

pub fn free_symbols_prop(prop: &Prop) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols_prop(prop, &mut symbols);
    symbols
}

fn add_free_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Equal(left, right) => {
            add_free_symbols(left, symbols);
            add_free_symbols(right, symbols);
        }
        Prop::IsValue(computation) => {
            add_free_symbols(computation, symbols);
        }
        Prop::IsList(computation) => {
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
        Prop::Equal(left, right) => Prop::Equal(
            rename_bound_var(left, old, new),
            rename_bound_var(right, old, new),
        ),
        Prop::IsValue(computation) => Prop::IsValue(rename_bound_var(computation, old, new)),
        Prop::IsList(computation) => Prop::IsList(rename_bound_var(computation, old, new)),
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

fn fresh_symbol_for_prop(prop: &Prop, replacement: &Computation, variable: Symbol) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols_prop(prop, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    let mut symbol = Symbol(0);
    while symbols.contains(&symbol) {
        symbol = Symbol(symbol.0 + 1);
    }
    symbol
}

fn add_all_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Equal(left, right) => {
            add_all_symbols(left, symbols);
            add_all_symbols(right, symbols);
        }
        Prop::IsValue(computation) => {
            add_all_symbols(computation, symbols);
        }
        Prop::IsList(computation) => {
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

fn context_mentions_symbol(context: &Context, symbol: Symbol) -> bool {
    context
        .values()
        .any(|prop| prop_mentions_symbol(prop, symbol))
}
