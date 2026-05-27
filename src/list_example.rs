//! A small list experiment built on the kernel.
//!
//! This deliberately proves concrete finite facts. The current kernel has no
//! recursive definitions or induction, so the fully general reverse theorem is
//! not expressible here yet.

use crate::{
    CaseBranch, EvalError, Field, Lambda, Proof, Prop, Record, Step, Symbol, Term, Variant, check,
    step,
};

pub const TRUE: Symbol = 1;
pub const FALSE: Symbol = 2;
pub const UNIT: Symbol = 3;

pub const NIL: Symbol = 10;
pub const CONS: Symbol = 11;

pub const HEAD: Symbol = 20;
pub const TAIL: Symbol = 21;

pub const ERROR_REVERSE_NEEDS_RECURSION: Symbol = 30;

const LIST: Symbol = 1_000;
const NIL_PAYLOAD: Symbol = 1_001;
const CELL: Symbol = 1_002;
const TAIL_PAYLOAD: Symbol = 1_003;
const REST_CELL: Symbol = 1_004;
const LOOP_ARGUMENT: Symbol = 1_005;

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

pub fn variant(tag: Symbol, value: Term) -> Term {
    Term::Variant(Variant {
        tag,
        value: Box::new(value),
    })
}

pub fn field(label: Symbol, value: Term) -> Field {
    Field { label, value }
}

pub fn record(fields: Record) -> Term {
    Term::Record(fields)
}

pub fn project(record: Term, label: Symbol) -> Term {
    Term::Project {
        record: Box::new(record),
        label,
    }
}

pub fn branch(tag: Symbol, parameter: Symbol, body: Term) -> CaseBranch {
    CaseBranch {
        tag,
        parameter,
        body,
    }
}

pub fn case(variant: Term, branches: Vec<CaseBranch>) -> Term {
    Term::Case {
        variant: Box::new(variant),
        branches,
    }
}

pub fn true_value() -> Term {
    quote(TRUE)
}

pub fn false_value() -> Term {
    quote(FALSE)
}

pub fn unit() -> Term {
    quote(UNIT)
}

pub fn error(symbol: Symbol) -> Term {
    Term::Error(Box::new(quote(symbol)))
}

pub fn nil() -> Term {
    variant(NIL, unit())
}

/// `cons` is represented as a sum case whose payload is a product.
pub fn cons(head: Term, tail: Term) -> Term {
    variant(CONS, record(vec![field(HEAD, head), field(TAIL, tail)]))
}

pub fn singleton(value: Term) -> Term {
    cons(value, nil())
}

pub fn pair(first: Term, second: Term) -> Term {
    cons(first, singleton(second))
}

/// A shallow list recognizer.
///
/// This recognizes `nil` and `cons` at the outer constructor. A recursive
/// `is_list` needs recursive definitions, which the kernel does not have yet.
pub fn is_list() -> Term {
    lambda(
        LIST,
        case(
            var(LIST),
            vec![
                branch(NIL, NIL_PAYLOAD, true_value()),
                branch(CONS, CELL, true_value()),
            ],
        ),
    )
}

pub fn is_list_call(value: Term) -> Term {
    apply(is_list(), value)
}

/// A bounded reverse experiment.
///
/// This reverses `nil` and singleton lists. Longer lists return an explicit
/// error marker because real reverse needs recursion.
pub fn reverse() -> Term {
    lambda(
        LIST,
        case(
            var(LIST),
            vec![
                branch(NIL, NIL_PAYLOAD, nil()),
                branch(
                    CONS,
                    CELL,
                    case(
                        project(var(CELL), TAIL),
                        vec![
                            branch(NIL, TAIL_PAYLOAD, cons(project(var(CELL), HEAD), nil())),
                            branch(CONS, REST_CELL, error(ERROR_REVERSE_NEEDS_RECURSION)),
                        ],
                    ),
                ),
            ],
        ),
    )
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
    use crate::{Context, Proof, check, check_in_context};

    const A: Symbol = 100;
    const B: Symbol = 101;
    const NOT_A_LIST: Symbol = 102;
    const ASSUMPTION: Symbol = 200;

    fn prove_evaluation(term: Term, expected: Term) -> Proof {
        proof_by_evaluation(term, expected, 64).expect("example should evaluate")
    }

    fn assert_evaluates(term: Term, expected: Term) {
        let proof = prove_evaluation(term.clone(), expected.clone());
        assert!(check_evaluates_to(term, expected, &proof));
    }

    #[test]
    fn is_list_accepts_nil_and_singleton() {
        assert_evaluates(is_list_call(nil()), true_value());
        assert_evaluates(is_list_call(singleton(quote(A))), true_value());
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
    fn reverse_pair_reaches_explicit_error_marker() {
        assert_evaluates(
            reverse_call(pair(quote(A), quote(B))),
            error(ERROR_REVERSE_NEEDS_RECURSION),
        );
    }

    #[test]
    fn reversed_nil_is_a_list() {
        assert_evaluates(is_list_call(reverse_call(nil())), true_value());
    }

    #[test]
    fn reversed_singleton_is_a_list() {
        let list = singleton(quote(A));

        assert_evaluates(is_list_call(reverse_call(list)), true_value());
    }

    #[test]
    fn concrete_implication_for_reverse_nil_termination() {
        let premise = evaluates_to(is_list_call(nil()), true_value());
        let conclusion = evaluates_to(reverse_call(nil()), nil());
        let conclusion_proof = prove_evaluation(reverse_call(nil()), nil());
        let proof = Proof::ImpliesIntro {
            assumption: ASSUMPTION,
            premise: premise.clone(),
            proof: Box::new(conclusion_proof),
        };

        assert!(check(
            &proof,
            &Prop::Implies(Box::new(premise), Box::new(conclusion))
        ));
    }

    #[test]
    fn concrete_implication_for_reversed_nil_is_list() {
        let premise = evaluates_to(is_list_call(nil()), true_value());
        let conclusion = evaluates_to(is_list_call(reverse_call(nil())), true_value());
        let conclusion_proof = prove_evaluation(is_list_call(reverse_call(nil())), true_value());
        let proof = Proof::ImpliesIntro {
            assumption: ASSUMPTION,
            premise: premise.clone(),
            proof: Box::new(conclusion_proof),
        };

        assert!(check(
            &proof,
            &Prop::Implies(Box::new(premise), Box::new(conclusion))
        ));
    }

    #[test]
    fn loop_forever_diverges() {
        let term = loop_forever_call();
        let proof = prove_evaluation(term.clone(), Term::Diverge);

        assert!(check(&proof, &diverges(term)));
    }

    #[test]
    fn non_list_input_still_hits_meta_evaluator_error() {
        assert_eq!(
            evaluation_chain(is_list_call(quote(NOT_A_LIST)), 64),
            Err(EvaluationProofError::Eval(EvalError::CaseNonVariant(
                quote(NOT_A_LIST)
            )))
        );
    }

    #[test]
    fn evaluation_proof_rejects_wrong_expected_value() {
        assert_eq!(
            proof_by_evaluation(reverse_call(nil()), true_value(), 64),
            Err(EvaluationProofError::UnexpectedNormalForm {
                expected: true_value(),
                actual: nil(),
            })
        );
    }

    #[test]
    fn general_reverse_theorem_is_not_available_from_concrete_facts() {
        let variable = var(9_999);
        let premise = evaluates_to(is_list_call(variable.clone()), true_value());
        let conclusion = evaluates_to(is_list_call(reverse_call(variable)), true_value());
        let context = Context::from([(ASSUMPTION, premise.clone())]);

        assert!(!check(&Proof::Assume(ASSUMPTION), &conclusion));
        assert!(!check_in_context(
            &Proof::Assume(ASSUMPTION),
            &conclusion,
            &context,
        ));
    }
}
