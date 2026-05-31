//! List definitions and theorems for the standard prelude.

use crate::{
    Lambda, ListCase, Name, Proof, Prop, Symbol, Term, Theorem, Theory, computes_to_list, forall,
    implies, is_list,
};

use super::{
    APPEND, APPEND_NIL_COMPUTES_TO_LIST, NIL_IS_LIST, REVERSE, REVERSE_ACC,
    REVERSE_ACC_COMPUTES_TO_LIST, REVERSE_COMPUTES_TO_LIST, REVERSE_NIL_COMPUTES_TO_LIST,
    source::{NameBinding, ParseError, ParsedModule, ParsedTheorem, SymbolBinding},
};

pub use super::proof::EvaluationProofError;

#[cfg(test)]
use super::source::ProofScript;

pub const UNIT: Symbol = Symbol(3);

const SOURCE: &str = include_str!("list.lisp");

const LIST: Symbol = Symbol(1_000);
const CELL: Symbol = Symbol(1_001);
const SELF: Symbol = Symbol(1_002);
const ACC: Symbol = Symbol(1_003);
const FIXED_POINT_FUNCTION: Symbol = Symbol(1_004);
const FIXED_POINT_SELF: Symbol = Symbol(1_005);
const FIXED_POINT_VALUE: Symbol = Symbol(1_006);
const LOOP_ARGUMENT: Symbol = Symbol(1_007);
const LEFT: Symbol = Symbol(1_008);
const RIGHT: Symbol = Symbol(1_009);

const TERM_DEFINITIONS: &[NameBinding] = &[
    NameBinding {
        spelling: "reverse_acc",
        name: REVERSE_ACC,
    },
    NameBinding {
        spelling: "reverse",
        name: REVERSE,
    },
    NameBinding {
        spelling: "append",
        name: APPEND,
    },
];

const THEOREM_DEFINITIONS: &[NameBinding] = &[
    NameBinding {
        spelling: "nil_is_list",
        name: NIL_IS_LIST,
    },
    NameBinding {
        spelling: "reverse_acc_computes_to_list",
        name: REVERSE_ACC_COMPUTES_TO_LIST,
    },
    NameBinding {
        spelling: "reverse_computes_to_list",
        name: REVERSE_COMPUTES_TO_LIST,
    },
    NameBinding {
        spelling: "reverse_nil_computes_to_list",
        name: REVERSE_NIL_COMPUTES_TO_LIST,
    },
    NameBinding {
        spelling: "append_nil_computes_to_list",
        name: APPEND_NIL_COMPUTES_TO_LIST,
    },
];

const TERM_SYMBOLS: &[SymbolBinding] = &[
    SymbolBinding {
        spelling: "unit",
        symbol: UNIT,
    },
    SymbolBinding {
        spelling: "list",
        symbol: LIST,
    },
    SymbolBinding {
        spelling: "cell",
        symbol: CELL,
    },
    SymbolBinding {
        spelling: "self",
        symbol: SELF,
    },
    SymbolBinding {
        spelling: "acc",
        symbol: ACC,
    },
    SymbolBinding {
        spelling: "fixed_point_function",
        symbol: FIXED_POINT_FUNCTION,
    },
    SymbolBinding {
        spelling: "fixed_point_self",
        symbol: FIXED_POINT_SELF,
    },
    SymbolBinding {
        spelling: "fixed_point_value",
        symbol: FIXED_POINT_VALUE,
    },
    SymbolBinding {
        spelling: "loop_argument",
        symbol: LOOP_ARGUMENT,
    },
    SymbolBinding {
        spelling: "left",
        symbol: LEFT,
    },
    SymbolBinding {
        spelling: "right",
        symbol: RIGHT,
    },
];

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

pub fn reverse_acc() -> Term {
    super::reverse_acc()
}

pub(super) fn module() -> Result<ParsedModule, ParseError> {
    super::source::parse_module(SOURCE, TERM_DEFINITIONS, THEOREM_DEFINITIONS, TERM_SYMBOLS)
}

pub fn reverse_acc_definition() -> Term {
    definition(REVERSE_ACC)
}

pub fn reverse() -> Term {
    super::reverse()
}

pub fn reverse_definition() -> Term {
    definition(REVERSE)
}

pub fn append() -> Term {
    super::append()
}

pub fn append_definition() -> Term {
    definition(APPEND)
}

fn definition(name: Name) -> Term {
    module()
        .expect("prelude list source should parse")
        .term(name)
        .cloned()
        .expect("prelude list source should define requested term")
}

pub fn reverse_acc_computes_to_list_source_theorem() -> Prop {
    theorem_prop(REVERSE_ACC_COMPUTES_TO_LIST)
}

pub fn nil_is_list_source_theorem() -> Prop {
    theorem_prop(NIL_IS_LIST)
}

pub fn reverse_computes_to_list_source_theorem() -> Prop {
    theorem_prop(REVERSE_COMPUTES_TO_LIST)
}

pub fn reverse_nil_computes_to_list_source_theorem() -> Prop {
    theorem_prop(REVERSE_NIL_COMPUTES_TO_LIST)
}

pub fn append_nil_computes_to_list_source_theorem() -> Prop {
    theorem_prop(APPEND_NIL_COMPUTES_TO_LIST)
}

fn theorem_prop(name: Name) -> Prop {
    theorem_definition(name).prop
}

fn theorem_definition(name: Name) -> ParsedTheorem {
    module()
        .expect("prelude list source should parse theorem statements")
        .theorem(name)
        .cloned()
        .expect("prelude list source should define requested theorem")
}

#[cfg(test)]
fn theorem_symbol(name: Name, spelling: &str) -> Symbol {
    theorem_definition(name)
        .symbol(spelling)
        .expect("prelude list source should define requested theorem symbol once")
}

#[cfg(test)]
pub(super) fn reverse_computes_to_list_source_result_symbol() -> Symbol {
    theorem_symbol(REVERSE_COMPUTES_TO_LIST, "result")
}

pub(super) fn checked_source_theorem(name: Name) -> Option<Theorem> {
    let module = module().ok()?;

    super::proof::source_theorem(module, name, super::term_theory())
}

pub fn reverse_call(value: Term) -> Term {
    apply(reverse(), value)
}

pub fn reverse_acc_call(list: Term, acc: Term) -> Term {
    apply(apply(reverse_acc(), list), acc)
}

pub fn append_call(left: Term, right: Term) -> Term {
    apply(apply(append(), left), right)
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

/// If `right` is a list, then `append(nil, right)` computes to a list.
pub fn append_nil_computes_to_list_theorem(right: Symbol, result: Symbol) -> Prop {
    forall(
        right,
        implies(
            is_list(var(right)),
            computes_to_list(result, append_call(nil(), var(right))),
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
    let theory = super::term_theory();
    evaluation_chain_in_theory(term, &theory, limit)
}

pub fn evaluation_chain_in_theory(
    term: Term,
    theory: &Theory,
    limit: usize,
) -> Result<Vec<Term>, EvaluationProofError> {
    super::proof::evaluation_chain_in_theory(term, theory, limit)
}

/// A small tactic that turns bounded evaluation into a `Proof::Steps` object.
///
/// This uses the prelude term theory. Use `proof_by_evaluation_in_theory`
/// for a custom theory.
pub fn proof_by_evaluation(
    term: Term,
    expected: Term,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let theory = super::term_theory();
    proof_by_evaluation_in_theory(term, expected, &theory, limit)
}

pub fn proof_by_evaluation_in_theory(
    term: Term,
    expected: Term,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    super::proof::proof_by_evaluation_in_theory(term, expected, theory, limit)
}

pub fn proof_by_reduction_in_theory(
    term: Term,
    expected: Term,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    super::proof::proof_by_reduction_in_theory(term, expected, theory, limit)
}

pub fn proof_by_same_normal_form_in_theory(
    left: Term,
    right: Term,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    super::proof::proof_by_same_normal_form_in_theory(left, right, theory, limit)
}

pub fn check_evaluates_to(term: Term, value: Term, proof: &Proof) -> bool {
    let theory = super::term_theory();
    check_evaluates_to_in_theory(term, value, proof, &theory)
}

pub fn check_evaluates_to_in_theory(
    term: Term,
    value: Term,
    proof: &Proof,
    theory: &Theory,
) -> bool {
    super::proof::check_evaluates_to_in_theory(term, value, proof, theory)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Proof, and, computes_to, diverges, exists};

    const A: Symbol = Symbol(100);
    const B: Symbol = Symbol(101);
    const NOT_A_LIST: Symbol = Symbol(102);
    const X: Symbol = Symbol(200);
    const ACCUMULATOR: Symbol = Symbol(201);
    const RESULT: Symbol = Symbol(202);

    fn prove_evaluation(term: Term, expected: Term) -> Proof {
        proof_by_evaluation(term, expected, 512).expect("example should evaluate")
    }

    fn assert_evaluates(term: Term, expected: Term) {
        let proof = prove_evaluation(term.clone(), expected.clone());
        assert!(check_evaluates_to(term, expected, &proof));
    }

    #[test]
    fn nil_source_theorem_has_expected_shape() {
        assert_eq!(nil_is_list_source_theorem(), is_list(nil()));
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
    fn reverse_acc_source_theorem_has_expected_shape() {
        let list = theorem_symbol(REVERSE_ACC_COMPUTES_TO_LIST, "list");
        let acc = theorem_symbol(REVERSE_ACC_COMPUTES_TO_LIST, "acc");
        let result = theorem_symbol(REVERSE_ACC_COMPUTES_TO_LIST, "result");

        assert_eq!(
            reverse_acc_computes_to_list_source_theorem(),
            reverse_acc_computes_to_list_theorem(list, acc, result)
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
    fn reverse_source_theorem_has_expected_shape() {
        let list = theorem_symbol(REVERSE_COMPUTES_TO_LIST, "list");
        let result = theorem_symbol(REVERSE_COMPUTES_TO_LIST, "result");

        assert_eq!(
            reverse_computes_to_list_source_theorem(),
            reverse_computes_to_list_theorem(list, result)
        );
    }

    #[test]
    fn reverse_nil_source_theorem_has_expected_shape() {
        let result = theorem_symbol(REVERSE_NIL_COMPUTES_TO_LIST, "result");

        assert_eq!(
            reverse_nil_computes_to_list_source_theorem(),
            computes_to_list(result, reverse_call(nil()))
        );
    }

    #[test]
    fn append_nil_computes_to_list_theorem_has_expected_shape() {
        assert_eq!(
            append_nil_computes_to_list_theorem(X, RESULT),
            forall(
                X,
                implies(
                    is_list(var(X)),
                    exists(
                        RESULT,
                        and(
                            computes_to(append_call(nil(), var(X)), var(RESULT)),
                            is_list(var(RESULT)),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn append_nil_source_theorem_has_expected_shape() {
        let right = theorem_symbol(APPEND_NIL_COMPUTES_TO_LIST, "right");
        let result = theorem_symbol(APPEND_NIL_COMPUTES_TO_LIST, "result");

        assert_eq!(
            append_nil_computes_to_list_source_theorem(),
            append_nil_computes_to_list_theorem(right, result)
        );
    }

    #[test]
    fn reverse_source_theorem_uses_source_proof_script() {
        assert!(matches!(
            theorem_definition(NIL_IS_LIST).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_ACC_COMPUTES_TO_LIST).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_COMPUTES_TO_LIST).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_NIL_COMPUTES_TO_LIST).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(APPEND_NIL_COMPUTES_TO_LIST).proof,
            ProofScript::Proof(_)
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
    fn append_nil_returns_right_list() {
        let list = pair(quote(A), quote(B));

        assert_evaluates(append_call(nil(), list.clone()), list);
    }

    #[test]
    fn append_pair_terminates_without_error() {
        assert_evaluates(
            append_call(pair(quote(A), quote(B)), singleton(quote(NOT_A_LIST))),
            triple(quote(A), quote(B), quote(NOT_A_LIST)),
        );
    }

    #[test]
    fn loop_forever_diverges() {
        let theory = crate::prelude::theory();
        let term = loop_forever_call();
        let proof = prove_evaluation(term.clone(), Term::Diverge);

        assert!(theory.check(&proof, &diverges(term)));
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
