//! List definitions and theorems for the standard prelude.

use crate::{
    Environment, Lambda, ListCase, Proof, Prop, Step, Symbol, Term, and, check_in_environment,
    computes_to, computes_to_list, forall, implies, is_list, normal_form_in_environment,
    step_in_environment,
};

pub const UNIT: Symbol = Symbol(3);

const LIST: Symbol = Symbol(1_000);
const CELL: Symbol = Symbol(1_001);
const SELF: Symbol = Symbol(1_002);
const ACC: Symbol = Symbol(1_003);
const FIXED_POINT_FUNCTION: Symbol = Symbol(1_004);
const FIXED_POINT_SELF: Symbol = Symbol(1_005);
const FIXED_POINT_VALUE: Symbol = Symbol(1_006);
const LOOP_ARGUMENT: Symbol = Symbol(1_007);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvaluationProofError {
    StepLimitExceeded { limit: usize },
    UnexpectedNormalForm { expected: Term, actual: Term },
}

pub fn quote(symbol: Symbol) -> Term {
    Term::Quote(symbol)
}

pub fn var(symbol: Symbol) -> Term {
    Term::Var(symbol)
}

pub fn lambda(parameter: Symbol, body: Term) -> Term {
    Term::Lambda(Lambda {
        parameter,
        body: Box::new(body),
    })
}

pub fn apply(function: Term, argument: Term) -> Term {
    Term::Apply {
        function: Box::new(function),
        argument: Box::new(argument),
    }
}

pub fn nil() -> Term {
    Term::Nil
}

pub fn cons(head: Term, tail: Term) -> Term {
    Term::Cons {
        head: Box::new(head),
        tail: Box::new(tail),
    }
}

pub fn head(term: Term) -> Term {
    Term::Head(Box::new(term))
}

pub fn tail(term: Term) -> Term {
    Term::Tail(Box::new(term))
}

pub fn list_case(list: Term, nil: Term, cons: Symbol, cons_case: Term) -> Term {
    Term::ListCase(ListCase {
        list: Box::new(list),
        nil: Box::new(nil),
        cons,
        cons_case: Box::new(cons_case),
    })
}

pub fn unit() -> Term {
    quote(UNIT)
}

pub fn error(symbol: Symbol) -> Term {
    Term::Error(Box::new(quote(symbol)))
}

pub fn singleton(value: Term) -> Term {
    cons(value, nil())
}

pub fn pair(first: Term, second: Term) -> Term {
    cons(first, singleton(second))
}

pub fn triple(first: Term, second: Term, third: Term) -> Term {
    cons(first, pair(second, third))
}

/// The call-by-value fixed-point combinator.
///
/// The ordinary Y combinator unfolds too eagerly under this evaluator; this Z
/// combinator delays the recursive self-reference under an extra lambda.
pub fn z_combinator() -> Term {
    lambda(
        FIXED_POINT_FUNCTION,
        apply(fixed_point_half(), fixed_point_half()),
    )
}

fn fixed_point_half() -> Term {
    lambda(
        FIXED_POINT_SELF,
        apply(
            var(FIXED_POINT_FUNCTION),
            lambda(
                FIXED_POINT_VALUE,
                apply(
                    apply(var(FIXED_POINT_SELF), var(FIXED_POINT_SELF)),
                    var(FIXED_POINT_VALUE),
                ),
            ),
        ),
    )
}

pub fn reverse_acc() -> Term {
    super::reverse_acc()
}

pub fn reverse_acc_definition() -> Term {
    apply(z_combinator(), reverse_acc_body())
}

fn reverse_acc_body() -> Term {
    lambda(
        SELF,
        lambda(
            LIST,
            lambda(
                ACC,
                list_case(
                    var(LIST),
                    var(ACC),
                    CELL,
                    apply(
                        apply(var(SELF), tail(var(CELL))),
                        cons(head(var(CELL)), var(ACC)),
                    ),
                ),
            ),
        ),
    )
}

pub fn reverse() -> Term {
    super::reverse()
}

pub fn reverse_definition() -> Term {
    lambda(LIST, reverse_acc_call(var(LIST), nil()))
}

pub fn reverse_call(value: Term) -> Term {
    apply(reverse(), value)
}

pub fn reverse_acc_call(list: Term, acc: Term) -> Term {
    apply(apply(reverse_acc(), list), acc)
}

/// If `list` and `acc` are lists, then `reverse_acc(list, acc)` computes to a list.
///
/// `result` names the existential result in `computes_to_list` and should be
/// distinct from `list` and `acc`.
pub fn reverse_acc_computes_to_list_theorem(list: Symbol, acc: Symbol, result: Symbol) -> Prop {
    forall(
        list,
        implies(
            is_list(var(list)),
            forall(
                acc,
                implies(
                    is_list(var(acc)),
                    computes_to_list(result, reverse_acc_call(var(list), var(acc))),
                ),
            ),
        ),
    )
}

/// If `list` is a list, then `reverse(list)` computes to a list.
///
/// `result` names the existential result in `computes_to_list` and should be
/// distinct from `list`.
pub fn reverse_computes_to_list_theorem(list: Symbol, result: Symbol) -> Prop {
    forall(
        list,
        implies(
            is_list(var(list)),
            computes_to_list(result, reverse_call(var(list))),
        ),
    )
}

/// A function whose result is the denotational divergence marker.
pub fn loop_forever() -> Term {
    lambda(LOOP_ARGUMENT, Term::Diverge)
}

pub fn loop_forever_call() -> Term {
    apply(loop_forever(), unit())
}

/// Build the concrete evaluator path using the prelude definitions.
pub fn evaluation_chain(term: Term, limit: usize) -> Result<Vec<Term>, EvaluationProofError> {
    let environment = super::term_environment();
    evaluation_chain_in_environment(term, &environment, limit)
}

/// Build the concrete evaluator path for a term, stopping at a normal form.
pub fn evaluation_chain_in_environment(
    term: Term,
    environment: &Environment,
    limit: usize,
) -> Result<Vec<Term>, EvaluationProofError> {
    let mut term = term;
    let mut chain = vec![term.clone()];

    for _ in 0..limit {
        match step_in_environment(&term, environment) {
            Step::Reduced(next) => {
                chain.push(next.clone());
                term = next;
            }
            Step::Normal => return Ok(chain),
        }
    }

    Err(EvaluationProofError::StepLimitExceeded { limit })
}

/// A small tactic that turns bounded evaluation into a `Proof::Steps` object.
///
/// This uses the prelude definitions. Use `proof_by_evaluation_in_environment`
/// for a custom environment.
pub fn proof_by_evaluation(
    term: Term,
    expected: Term,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let environment = super::term_environment();
    proof_by_evaluation_in_environment(term, expected, &environment, limit)
}

pub fn proof_by_evaluation_in_environment(
    term: Term,
    expected: Term,
    environment: &Environment,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let chain = evaluation_chain_in_environment(term, environment, limit)?;
    let actual = chain
        .last()
        .cloned()
        .expect("evaluation chains are nonempty");

    if actual != expected {
        return Err(EvaluationProofError::UnexpectedNormalForm { expected, actual });
    }

    Ok(Proof::Steps(chain))
}

pub fn check_evaluates_to(term: Term, value: Term, proof: &Proof) -> bool {
    let environment = super::term_environment();
    check_evaluates_to_in_environment(term, value, proof, &environment)
}

pub fn check_evaluates_to_in_environment(
    term: Term,
    value: Term,
    proof: &Proof,
    environment: &Environment,
) -> bool {
    check_in_environment(proof, &computes_to(term, value), environment)
}

/// Proves `reverse_acc_computes_to_list_theorem(list, acc, result)`.
///
/// `list`, `acc`, and `result` should be distinct theorem variables. Internal
/// proof symbols are generated fresh from those inputs.
pub fn reverse_acc_computes_to_list_proof(list: Symbol, acc: Symbol, result: Symbol) -> Proof {
    let mut used = reserved_proof_symbols();
    let symbols = fresh_reverse_acc_proof_symbols(list, acc, result, &mut used);

    reverse_acc_computes_to_list_proof_with_symbols(symbols)
}

/// Proves `reverse_computes_to_list_theorem(input, result)`.
///
/// `input` and `result` should be distinct theorem variables. Internal proof
/// symbols are generated fresh from those inputs.
pub fn reverse_computes_to_list_proof(input: Symbol, result: Symbol) -> Proof {
    let mut used = reserved_proof_symbols();
    add_used_symbol(&mut used, input);
    add_used_symbol(&mut used, result);

    let input_is_list_assumption = next_fresh_symbol(&mut used);
    let accumulator_theorem_list = next_fresh_symbol(&mut used);
    let accumulator = next_fresh_symbol(&mut used);
    let accumulator_symbols =
        fresh_reverse_acc_proof_symbols(accumulator_theorem_list, accumulator, result, &mut used);
    let rewrite_target = next_fresh_symbol(&mut used);

    reverse_computes_to_list_proof_with_symbols(ReverseProofSymbols {
        input,
        result,
        input_is_list_assumption,
        accumulator_symbols,
        rewrite_target,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ReverseAccProofSymbols {
    list: Symbol,
    acc: Symbol,
    result: Symbol,
    acc_is_list_assumption: Symbol,
    head: Symbol,
    tail: Symbol,
    head_is_value_assumption: Symbol,
    tail_is_list_assumption: Symbol,
    induction_hypothesis_assumption: Symbol,
    rewrite_target: Symbol,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ReverseProofSymbols {
    input: Symbol,
    result: Symbol,
    input_is_list_assumption: Symbol,
    accumulator_symbols: ReverseAccProofSymbols,
    rewrite_target: Symbol,
}

fn reserved_proof_symbols() -> Vec<Symbol> {
    vec![
        UNIT,
        LIST,
        CELL,
        SELF,
        ACC,
        FIXED_POINT_FUNCTION,
        FIXED_POINT_SELF,
        FIXED_POINT_VALUE,
        LOOP_ARGUMENT,
    ]
}

fn fresh_reverse_acc_proof_symbols(
    list: Symbol,
    acc: Symbol,
    result: Symbol,
    used: &mut Vec<Symbol>,
) -> ReverseAccProofSymbols {
    add_used_symbol(used, list);
    add_used_symbol(used, acc);
    add_used_symbol(used, result);

    ReverseAccProofSymbols {
        list,
        acc,
        result,
        acc_is_list_assumption: next_fresh_symbol(used),
        head: next_fresh_symbol(used),
        tail: next_fresh_symbol(used),
        head_is_value_assumption: next_fresh_symbol(used),
        tail_is_list_assumption: next_fresh_symbol(used),
        induction_hypothesis_assumption: next_fresh_symbol(used),
        rewrite_target: next_fresh_symbol(used),
    }
}

fn add_used_symbol(used: &mut Vec<Symbol>, symbol: Symbol) {
    if !used.contains(&symbol) {
        used.push(symbol);
    }
}

fn next_fresh_symbol(used: &mut Vec<Symbol>) -> Symbol {
    let mut symbol = Symbol(0);
    while used.contains(&symbol) {
        symbol = Symbol(symbol.0 + 1);
    }

    used.push(symbol);
    symbol
}

fn reverse_acc_nil_base_proof(acc: Symbol, result: Symbol, assumption: Symbol) -> Proof {
    let term = reverse_acc_call(nil(), var(acc));
    let result_body = and(computes_to(term.clone(), var(result)), is_list(var(result)));
    let environment = super::term_environment();
    let evaluation = proof_by_evaluation_in_environment(term, var(acc), &environment, 128)
        .expect("base case should reduce");

    Proof::ForAllIntro {
        variable: acc,
        proof: Box::new(Proof::ImpliesIntro {
            assumption,
            premise: is_list(var(acc)),
            proof: Box::new(Proof::ExistsIntro {
                variable: result,
                body: result_body,
                witness: var(acc),
                proof: Box::new(Proof::AndIntro(
                    Box::new(evaluation),
                    Box::new(Proof::Assume(assumption)),
                )),
            }),
        }),
    }
}

fn reverse_acc_cons_unfolding_proof(head: Symbol, tail: Symbol, acc: Symbol) -> Proof {
    let start = reverse_acc_call(cons(var(head), var(tail)), var(acc));
    let recursive = reverse_acc_call(var(tail), cons(var(head), var(acc)));
    let environment = super::term_environment();
    let normal = normal_form_in_environment(&recursive, &environment);
    let start_to_normal =
        proof_by_evaluation_in_environment(start, normal.clone(), &environment, 128)
            .expect("start should unfold");
    let recursive_to_normal =
        proof_by_evaluation_in_environment(recursive, normal, &environment, 128)
            .expect("recursive call should unfold");

    Proof::Trans(
        Box::new(start_to_normal),
        Box::new(Proof::Symm(Box::new(recursive_to_normal))),
    )
}

fn reverse_acc_cons_step_proof(symbols: ReverseAccProofSymbols) -> Proof {
    let recursive_acc = cons(var(symbols.head), var(symbols.acc));
    let accumulator_is_list = Proof::ListCons {
        head: var(symbols.head),
        tail: var(symbols.acc),
        head_is_value: Box::new(Proof::Assume(symbols.head_is_value_assumption)),
        tail_is_list: Box::new(Proof::Assume(symbols.acc_is_list_assumption)),
    };
    let induction_hypothesis = Proof::ImpliesElim {
        implication: Box::new(Proof::ForAllElim {
            forall: Box::new(Proof::Assume(symbols.induction_hypothesis_assumption)),
            argument: recursive_acc,
        }),
        premise: Box::new(accumulator_is_list),
    };
    let rewrite = Proof::Rewrite {
        equality: Box::new(Proof::Symm(Box::new(reverse_acc_cons_unfolding_proof(
            symbols.head,
            symbols.tail,
            symbols.acc,
        )))),
        proof: Box::new(induction_hypothesis),
        variable: symbols.rewrite_target,
        template: computes_to_list(symbols.result, var(symbols.rewrite_target)),
    };

    Proof::ForAllIntro {
        variable: symbols.acc,
        proof: Box::new(Proof::ImpliesIntro {
            assumption: symbols.acc_is_list_assumption,
            premise: is_list(var(symbols.acc)),
            proof: Box::new(rewrite),
        }),
    }
}

fn reverse_acc_computes_to_list_proof_with_symbols(symbols: ReverseAccProofSymbols) -> Proof {
    let property = forall(
        symbols.acc,
        implies(
            is_list(var(symbols.acc)),
            computes_to_list(
                symbols.result,
                reverse_acc_call(var(symbols.list), var(symbols.acc)),
            ),
        ),
    );

    Proof::ListInduction {
        variable: symbols.list,
        property,
        base: Box::new(reverse_acc_nil_base_proof(
            symbols.acc,
            symbols.result,
            symbols.acc_is_list_assumption,
        )),
        head: symbols.head,
        tail: symbols.tail,
        head_is_value_assumption: symbols.head_is_value_assumption,
        tail_is_list_assumption: symbols.tail_is_list_assumption,
        induction_hypothesis_assumption: symbols.induction_hypothesis_assumption,
        step: Box::new(reverse_acc_cons_step_proof(symbols)),
    }
}

fn reverse_computes_to_list_proof_with_symbols(symbols: ReverseProofSymbols) -> Proof {
    let accumulator_theorem =
        reverse_acc_computes_to_list_proof_with_symbols(symbols.accumulator_symbols);
    let start = reverse_call(var(symbols.input));
    let unfolded = apply(reverse_definition(), var(symbols.input));
    let accumulator_call = reverse_acc_call(var(symbols.input), nil());
    let accumulator_result = Proof::ImpliesElim {
        implication: Box::new(Proof::ForAllElim {
            forall: Box::new(Proof::ImpliesElim {
                implication: Box::new(Proof::ForAllElim {
                    forall: Box::new(accumulator_theorem),
                    argument: var(symbols.input),
                }),
                premise: Box::new(Proof::Assume(symbols.input_is_list_assumption)),
            }),
            argument: nil(),
        }),
        premise: Box::new(Proof::ListNil),
    };
    let rewrite = Proof::Rewrite {
        equality: Box::new(Proof::Symm(Box::new(Proof::Steps(vec![
            start,
            unfolded,
            accumulator_call,
        ])))),
        proof: Box::new(accumulator_result),
        variable: symbols.rewrite_target,
        template: computes_to_list(symbols.result, var(symbols.rewrite_target)),
    };

    Proof::ForAllIntro {
        variable: symbols.input,
        proof: Box::new(Proof::ImpliesIntro {
            assumption: symbols.input_is_list_assumption,
            premise: is_list(var(symbols.input)),
            proof: Box::new(rewrite),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Proof, diverges, exists};

    const A: Symbol = Symbol(100);
    const B: Symbol = Symbol(101);
    const NOT_A_LIST: Symbol = Symbol(102);
    const X: Symbol = Symbol(200);
    const ACCUMULATOR: Symbol = Symbol(201);
    const RESULT: Symbol = Symbol(202);
    const HEAD: Symbol = Symbol(203);
    const TAIL: Symbol = Symbol(204);
    const ACCUMULATOR_IS_LIST: Symbol = Symbol(205);

    fn prove_evaluation(term: Term, expected: Term) -> Proof {
        proof_by_evaluation(term, expected, 512).expect("example should evaluate")
    }

    fn assert_evaluates(term: Term, expected: Term) {
        let proof = prove_evaluation(term.clone(), expected.clone());
        assert!(check_evaluates_to(term, expected, &proof));
    }

    #[test]
    fn reverse_acc_computes_to_list_theorem_has_expected_shape() {
        assert_eq!(
            reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
            forall(
                X,
                implies(
                    is_list(var(X)),
                    forall(
                        ACCUMULATOR,
                        implies(
                            is_list(var(ACCUMULATOR)),
                            exists(
                                RESULT,
                                and(
                                    computes_to(
                                        reverse_acc_call(var(X), var(ACCUMULATOR)),
                                        var(RESULT),
                                    ),
                                    is_list(var(RESULT)),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_computes_to_list_theorem_has_expected_shape() {
        assert_eq!(
            reverse_computes_to_list_theorem(X, RESULT),
            forall(
                X,
                implies(
                    is_list(var(X)),
                    exists(
                        RESULT,
                        and(
                            computes_to(reverse_call(var(X)), var(RESULT)),
                            is_list(var(RESULT)),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_acc_nil_base_case_is_provable() {
        let environment = crate::prelude::environment();
        let theorem_base = forall(
            ACCUMULATOR,
            implies(
                is_list(var(ACCUMULATOR)),
                computes_to_list(RESULT, reverse_acc_call(nil(), var(ACCUMULATOR))),
            ),
        );

        assert!(check_in_environment(
            &reverse_acc_nil_base_proof(ACCUMULATOR, RESULT, ACCUMULATOR_IS_LIST),
            &theorem_base,
            &environment,
        ));
    }

    #[test]
    fn reverse_acc_cons_case_symbolically_unfolds() {
        let environment = crate::prelude::environment();
        let start = reverse_acc_call(cons(var(HEAD), var(TAIL)), var(ACCUMULATOR));
        let recursive = reverse_acc_call(var(TAIL), cons(var(HEAD), var(ACCUMULATOR)));
        let proof = reverse_acc_cons_unfolding_proof(HEAD, TAIL, ACCUMULATOR);

        assert!(check_in_environment(
            &proof,
            &computes_to(start, recursive),
            &environment,
        ));
    }

    #[test]
    fn proves_reverse_acc_computes_to_list_for_all_lists() {
        let environment = crate::prelude::environment();
        let proof = reverse_acc_computes_to_list_proof(X, ACCUMULATOR, RESULT);

        assert!(check_in_environment(
            &proof,
            &reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
            &environment,
        ));
    }

    #[test]
    fn proves_reverse_computes_to_list_for_all_lists() {
        let environment = crate::prelude::environment();
        let proof = reverse_computes_to_list_proof(X, RESULT);

        assert!(check_in_environment(
            &proof,
            &reverse_computes_to_list_theorem(X, RESULT),
            &environment,
        ));
    }

    #[test]
    fn reverse_nil_terminates_without_error() {
        assert_evaluates(reverse_call(nil()), nil());
    }

    #[test]
    fn reverse_singleton_terminates_without_error() {
        let list = singleton(quote(A));

        assert_evaluates(reverse_call(list.clone()), list);
    }

    #[test]
    fn reverse_pair_terminates_without_error() {
        assert_evaluates(
            reverse_call(pair(quote(A), quote(B))),
            pair(quote(B), quote(A)),
        );
    }

    #[test]
    fn reverse_triple_terminates_without_error() {
        assert_evaluates(
            reverse_call(triple(quote(A), quote(B), quote(NOT_A_LIST))),
            triple(quote(NOT_A_LIST), quote(B), quote(A)),
        );
    }

    #[test]
    fn loop_forever_diverges() {
        let environment = crate::prelude::environment();
        let term = loop_forever_call();
        let proof = prove_evaluation(term.clone(), Term::Diverge);

        assert!(check_in_environment(&proof, &diverges(term), &environment));
    }

    #[test]
    fn reverse_non_list_input_reduces_to_error() {
        assert_evaluates(reverse_call(quote(NOT_A_LIST)), error(NOT_A_LIST));
    }

    #[test]
    fn reverse_malformed_tail_reduces_to_error() {
        assert_evaluates(
            reverse_call(cons(quote(A), quote(NOT_A_LIST))),
            error(NOT_A_LIST),
        );
    }

    #[test]
    fn evaluation_proof_rejects_wrong_expected_value() {
        assert_eq!(
            proof_by_evaluation(reverse_call(nil()), quote(NOT_A_LIST), 64),
            Err(EvaluationProofError::UnexpectedNormalForm {
                expected: quote(NOT_A_LIST),
                actual: nil(),
            })
        );
    }
}
