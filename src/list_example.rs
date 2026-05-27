//! A small list experiment built on the cons/nil kernel.
//!
//! This proves concrete finite facts about `reverse` with `Proof::Steps`.
//! General reverse theorems should use the kernel's list proposition and
//! induction rule rather than a userspace list recognizer.

use crate::{EvalError, Lambda, ListCase, Proof, Prop, Step, Symbol, Term, check, step};

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
    Eval(EvalError),
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
    lambda(LIST, apply(apply(reverse_acc(), var(LIST)), nil()))
}

pub fn reverse_call(value: Term) -> Term {
    apply(reverse(), value)
}

/// A function whose result is the denotational divergence marker.
pub fn loop_forever() -> Term {
    lambda(LOOP_ARGUMENT, Term::Diverge)
}

pub fn loop_forever_call() -> Term {
    apply(loop_forever(), unit())
}

pub fn evaluates_to(term: Term, value: Term) -> Prop {
    Prop::Equal(term, value)
}

pub fn diverges(term: Term) -> Prop {
    Prop::Equal(term, Term::Diverge)
}

/// Build the concrete evaluator path for a term, stopping at a normal form.
pub fn evaluation_chain(term: Term, limit: usize) -> Result<Vec<Term>, EvaluationProofError> {
    let mut term = term;
    let mut chain = vec![term.clone()];

    for _ in 0..limit {
        match step(&term).map_err(EvaluationProofError::Eval)? {
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
    check(proof, &evaluates_to(term, value))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Proof, check};

    const A: Symbol = 100;
    const B: Symbol = 101;
    const NOT_A_LIST: Symbol = 102;

    fn prove_evaluation(term: Term, expected: Term) -> Proof {
        proof_by_evaluation(term, expected, 512).expect("example should evaluate")
    }

    fn assert_evaluates(term: Term, expected: Term) {
        let proof = prove_evaluation(term.clone(), expected.clone());
        assert!(check_evaluates_to(term, expected, &proof));
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
    fn reverse_non_list_input_hits_meta_evaluator_error() {
        assert_eq!(
            evaluation_chain(reverse_call(quote(NOT_A_LIST)), 512),
            Err(EvaluationProofError::Eval(EvalError::CaseNonList(quote(
                NOT_A_LIST
            ))))
        );
    }

    #[test]
    fn reverse_malformed_tail_hits_meta_evaluator_error() {
        assert_eq!(
            evaluation_chain(reverse_call(cons(quote(A), quote(NOT_A_LIST))), 512),
            Err(EvaluationProofError::Eval(EvalError::CaseNonList(quote(
                NOT_A_LIST
            ))))
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
