//! A small list experiment built on the cons/nil kernel.
//!
//! This proves concrete finite facts about `reverse` with `Proof::Steps`.
//! General reverse theorems should use the kernel's list proposition and
//! induction rule rather than a userspace list recognizer.

use crate::{
    Lambda, ListCase, Proof, Prop, Step, Symbol, Term, check, computes_to, computes_to_list,
    forall, implies, is_list, step,
};

pub const UNIT: Symbol = 3;

const LIST: Symbol = 1_000;
const CELL: Symbol = 1_001;
const SELF: Symbol = 1_002;
const ACC: Symbol = 1_003;
const FIXED_POINT_FUNCTION: Symbol = 1_004;
const FIXED_POINT_SELF: Symbol = 1_005;
const FIXED_POINT_VALUE: Symbol = 1_006;
const LOOP_ARGUMENT: Symbol = 1_007;

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

/// Build the concrete evaluator path for a term, stopping at a normal form.
pub fn evaluation_chain(term: Term, limit: usize) -> Result<Vec<Term>, EvaluationProofError> {
    let mut term = term;
    let mut chain = vec![term.clone()];

    for _ in 0..limit {
        match step(&term) {
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
pub fn proof_by_evaluation(
    term: Term,
    expected: Term,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let chain = evaluation_chain(term, limit)?;
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
    check(proof, &computes_to(term, value))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Proof, and, check, diverges, exists, normal_form};

    const A: Symbol = 100;
    const B: Symbol = 101;
    const NOT_A_LIST: Symbol = 102;
    const X: Symbol = 200;
    const ACCUMULATOR: Symbol = 201;
    const RESULT: Symbol = 202;
    const HEAD: Symbol = 203;
    const TAIL: Symbol = 204;
    const ACCUMULATOR_IS_LIST: Symbol = 205;
    const HEAD_IS_VALUE: Symbol = 206;
    const TAIL_IS_LIST: Symbol = 207;
    const INDUCTION_HYPOTHESIS: Symbol = 208;
    const REWRITE_TARGET: Symbol = 209;
    const ACCUMULATOR_THEOREM_LIST: Symbol = 210;
    const REVERSE_INPUT_IS_LIST: Symbol = 211;
    const PUBLIC_REWRITE_TARGET: Symbol = 212;

    fn prove_evaluation(term: Term, expected: Term) -> Proof {
        proof_by_evaluation(term, expected, 512).expect("example should evaluate")
    }

    fn assert_evaluates(term: Term, expected: Term) {
        let proof = prove_evaluation(term.clone(), expected.clone());
        assert!(check_evaluates_to(term, expected, &proof));
    }

    fn reverse_acc_nil_base_proof(acc: Symbol, result: Symbol, assumption: Symbol) -> Proof {
        let term = reverse_acc_call(nil(), var(acc));
        let result_body = and(computes_to(term.clone(), var(result)), is_list(var(result)));
        let evaluation = proof_by_evaluation(term, var(acc), 128).expect("base case should reduce");

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
        let normal = normal_form(&recursive);
        let start_to_normal =
            proof_by_evaluation(start, normal.clone(), 128).expect("start should unfold");
        let recursive_to_normal =
            proof_by_evaluation(recursive, normal, 128).expect("recursive call should unfold");

        Proof::Trans(
            Box::new(start_to_normal),
            Box::new(Proof::Symm(Box::new(recursive_to_normal))),
        )
    }

    fn reverse_acc_cons_step_proof(
        head: Symbol,
        tail: Symbol,
        acc: Symbol,
        result: Symbol,
        acc_is_list_assumption: Symbol,
        head_is_value_assumption: Symbol,
        induction_hypothesis_assumption: Symbol,
    ) -> Proof {
        let recursive_acc = cons(var(head), var(acc));
        let accumulator_is_list = Proof::ListCons {
            head: var(head),
            tail: var(acc),
            head_is_value: Box::new(Proof::Assume(head_is_value_assumption)),
            tail_is_list: Box::new(Proof::Assume(acc_is_list_assumption)),
        };
        let induction_hypothesis = Proof::ImpliesElim {
            implication: Box::new(Proof::ForAllElim {
                forall: Box::new(Proof::Assume(induction_hypothesis_assumption)),
                argument: recursive_acc,
            }),
            premise: Box::new(accumulator_is_list),
        };
        let rewrite = Proof::Rewrite {
            equality: Box::new(Proof::Symm(Box::new(reverse_acc_cons_unfolding_proof(
                head, tail, acc,
            )))),
            proof: Box::new(induction_hypothesis),
            variable: REWRITE_TARGET,
            template: computes_to_list(result, var(REWRITE_TARGET)),
        };

        Proof::ForAllIntro {
            variable: acc,
            proof: Box::new(Proof::ImpliesIntro {
                assumption: acc_is_list_assumption,
                premise: is_list(var(acc)),
                proof: Box::new(rewrite),
            }),
        }
    }

    fn reverse_acc_computes_to_list_proof(
        list: Symbol,
        acc: Symbol,
        result: Symbol,
        acc_is_list_assumption: Symbol,
        head: Symbol,
        tail: Symbol,
        head_is_value_assumption: Symbol,
        tail_is_list_assumption: Symbol,
        induction_hypothesis_assumption: Symbol,
    ) -> Proof {
        let property = forall(
            acc,
            implies(
                is_list(var(acc)),
                computes_to_list(result, reverse_acc_call(var(list), var(acc))),
            ),
        );

        Proof::ListInduction {
            variable: list,
            property,
            base: Box::new(reverse_acc_nil_base_proof(
                acc,
                result,
                acc_is_list_assumption,
            )),
            head,
            tail,
            head_is_value_assumption,
            tail_is_list_assumption,
            induction_hypothesis_assumption,
            step: Box::new(reverse_acc_cons_step_proof(
                head,
                tail,
                acc,
                result,
                acc_is_list_assumption,
                head_is_value_assumption,
                induction_hypothesis_assumption,
            )),
        }
    }

    fn reverse_computes_to_list_proof(
        input: Symbol,
        result: Symbol,
        input_is_list_assumption: Symbol,
    ) -> Proof {
        let accumulator_theorem = reverse_acc_computes_to_list_proof(
            ACCUMULATOR_THEOREM_LIST,
            ACCUMULATOR,
            result,
            ACCUMULATOR_IS_LIST,
            HEAD,
            TAIL,
            HEAD_IS_VALUE,
            TAIL_IS_LIST,
            INDUCTION_HYPOTHESIS,
        );
        let accumulator_result = Proof::ImpliesElim {
            implication: Box::new(Proof::ForAllElim {
                forall: Box::new(Proof::ImpliesElim {
                    implication: Box::new(Proof::ForAllElim {
                        forall: Box::new(accumulator_theorem),
                        argument: var(input),
                    }),
                    premise: Box::new(Proof::Assume(input_is_list_assumption)),
                }),
                argument: nil(),
            }),
            premise: Box::new(Proof::ListNil),
        };
        let rewrite = Proof::Rewrite {
            equality: Box::new(Proof::Symm(Box::new(Proof::Step(reverse_call(var(input)))))),
            proof: Box::new(accumulator_result),
            variable: PUBLIC_REWRITE_TARGET,
            template: computes_to_list(result, var(PUBLIC_REWRITE_TARGET)),
        };

        Proof::ForAllIntro {
            variable: input,
            proof: Box::new(Proof::ImpliesIntro {
                assumption: input_is_list_assumption,
                premise: is_list(var(input)),
                proof: Box::new(rewrite),
            }),
        }
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
        let theorem_base = forall(
            ACCUMULATOR,
            implies(
                is_list(var(ACCUMULATOR)),
                computes_to_list(RESULT, reverse_acc_call(nil(), var(ACCUMULATOR))),
            ),
        );

        assert!(check(
            &reverse_acc_nil_base_proof(ACCUMULATOR, RESULT, ACCUMULATOR_IS_LIST),
            &theorem_base,
        ));
    }

    #[test]
    fn reverse_acc_cons_case_symbolically_unfolds() {
        let start = reverse_acc_call(cons(var(HEAD), var(TAIL)), var(ACCUMULATOR));
        let recursive = reverse_acc_call(var(TAIL), cons(var(HEAD), var(ACCUMULATOR)));
        let proof = reverse_acc_cons_unfolding_proof(HEAD, TAIL, ACCUMULATOR);

        assert!(check(&proof, &computes_to(start, recursive)));
    }

    #[test]
    fn proves_reverse_acc_computes_to_list_for_all_lists() {
        let proof = reverse_acc_computes_to_list_proof(
            X,
            ACCUMULATOR,
            RESULT,
            ACCUMULATOR_IS_LIST,
            HEAD,
            TAIL,
            HEAD_IS_VALUE,
            TAIL_IS_LIST,
            INDUCTION_HYPOTHESIS,
        );

        assert!(check(
            &proof,
            &reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
        ));
    }

    #[test]
    fn proves_reverse_computes_to_list_for_all_lists() {
        let proof = reverse_computes_to_list_proof(X, RESULT, REVERSE_INPUT_IS_LIST);

        assert!(check(&proof, &reverse_computes_to_list_theorem(X, RESULT)));
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
        let term = loop_forever_call();
        let proof = prove_evaluation(term.clone(), Term::Diverge);

        assert!(check(&proof, &diverges(term)));
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
