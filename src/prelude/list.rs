//! List definitions and theorems for the standard prelude.

use crate::{
    Computation, ErrorName, Lambda, ListCase, Name, Outcome, Proof, Prop, Symbol, Theorem, Theory,
    computes_to, computes_to_list, forall_where, is_list, is_value,
};

use super::{
    APPEND, APPEND_ASSOC, APPEND_COMPUTES_TO_LIST, APPEND_CONS, APPEND_NIL_COMPUTES_TO_LIST,
    APPEND_NIL_RETURNS_RIGHT, APPEND_RIGHT_NIL, APPEND_SINGLETON, REVERSE, REVERSE_ACC,
    REVERSE_ACC_COMPUTES_TO_LIST, REVERSE_COMPUTES_TO_LIST, REVERSE_NIL_COMPUTES_TO_LIST,
    SourceTheoremError,
    source::{ModuleSpec, ParseError, ParsedModule, ParsedTheorem, SymbolBinding},
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

pub(super) const MODULE: ModuleSpec = ModuleSpec {
    source: SOURCE,
    computation_definitions: &[
        super::source::NameBinding {
            spelling: "reverse_acc",
            name: REVERSE_ACC,
        },
        super::source::NameBinding {
            spelling: "reverse",
            name: REVERSE,
        },
        super::source::NameBinding {
            spelling: "append",
            name: APPEND,
        },
    ],
    theorem_definitions: &[
        super::source::NameBinding {
            spelling: "reverse_acc_computes_to_list",
            name: REVERSE_ACC_COMPUTES_TO_LIST,
        },
        super::source::NameBinding {
            spelling: "reverse_computes_to_list",
            name: REVERSE_COMPUTES_TO_LIST,
        },
        super::source::NameBinding {
            spelling: "reverse_nil_computes_to_list",
            name: REVERSE_NIL_COMPUTES_TO_LIST,
        },
        super::source::NameBinding {
            spelling: "append_nil_computes_to_list",
            name: APPEND_NIL_COMPUTES_TO_LIST,
        },
        super::source::NameBinding {
            spelling: "append_computes_to_list",
            name: APPEND_COMPUTES_TO_LIST,
        },
        super::source::NameBinding {
            spelling: "append_nil_returns_right",
            name: APPEND_NIL_RETURNS_RIGHT,
        },
        super::source::NameBinding {
            spelling: "append_right_nil",
            name: APPEND_RIGHT_NIL,
        },
        super::source::NameBinding {
            spelling: "append_cons",
            name: APPEND_CONS,
        },
        super::source::NameBinding {
            spelling: "append_singleton",
            name: APPEND_SINGLETON,
        },
        super::source::NameBinding {
            spelling: "append_assoc",
            name: APPEND_ASSOC,
        },
    ],
    symbols: &[
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
    ],
};

pub fn quote(symbol: Symbol) -> Computation {
    Computation::Quote(symbol)
}

pub fn var(symbol: Symbol) -> Computation {
    Computation::Var(symbol)
}

pub fn lambda(parameter: Symbol, body: Computation) -> Computation {
    Computation::Lambda(Lambda {
        parameter,
        body: Box::new(body),
    })
}

pub fn apply(function: Computation, argument: Computation) -> Computation {
    Computation::Apply {
        function: Box::new(function),
        argument: Box::new(argument),
    }
}

pub fn nil() -> Computation {
    Computation::Nil
}

pub fn cons(head: Computation, tail: Computation) -> Computation {
    Computation::Cons {
        head: Box::new(head),
        tail: Box::new(tail),
    }
}

pub fn head(computation: Computation) -> Computation {
    Computation::Head(Box::new(computation))
}

pub fn tail(computation: Computation) -> Computation {
    Computation::Tail(Box::new(computation))
}

pub fn list_case(
    list: Computation,
    nil: Computation,
    cons: Symbol,
    cons_case: Computation,
) -> Computation {
    Computation::ListCase(ListCase {
        list: Box::new(list),
        nil: Box::new(nil),
        cons,
        cons_case: Box::new(cons_case),
    })
}

pub fn unit() -> Computation {
    quote(UNIT)
}

pub fn error(name: ErrorName) -> Computation {
    Computation::Error(name)
}

pub fn singleton(value: Computation) -> Computation {
    cons(value, nil())
}

pub fn pair(first: Computation, second: Computation) -> Computation {
    cons(first, singleton(second))
}

pub fn triple(first: Computation, second: Computation, third: Computation) -> Computation {
    cons(first, pair(second, third))
}

pub fn reverse_acc() -> Computation {
    super::reverse_acc()
}

pub(super) fn module() -> Result<ParsedModule, ParseError> {
    MODULE.parse()
}

pub fn reverse_acc_definition() -> Computation {
    definition(REVERSE_ACC)
}

pub fn reverse() -> Computation {
    super::reverse()
}

pub fn reverse_definition() -> Computation {
    definition(REVERSE)
}

pub fn append() -> Computation {
    super::append()
}

pub fn append_definition() -> Computation {
    definition(APPEND)
}

fn definition(name: Name) -> Computation {
    module()
        .expect("prelude list source should parse")
        .computation(name)
        .cloned()
        .expect("prelude list source should define requested computation")
}

pub fn reverse_acc_computes_to_list_source_theorem() -> Prop {
    theorem_prop(REVERSE_ACC_COMPUTES_TO_LIST)
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

pub fn append_computes_to_list_source_theorem() -> Prop {
    theorem_prop(APPEND_COMPUTES_TO_LIST)
}

pub fn append_nil_returns_right_source_theorem() -> Prop {
    theorem_prop(APPEND_NIL_RETURNS_RIGHT)
}

pub fn append_right_nil_source_theorem() -> Prop {
    theorem_prop(APPEND_RIGHT_NIL)
}

pub fn append_cons_source_theorem() -> Prop {
    theorem_prop(APPEND_CONS)
}

pub fn append_singleton_source_theorem() -> Prop {
    theorem_prop(APPEND_SINGLETON)
}

pub fn append_assoc_source_theorem() -> Prop {
    theorem_prop(APPEND_ASSOC)
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
    checked_source_theorem_result(name).ok()
}

pub(super) fn checked_source_theorem_result(name: Name) -> Result<Theorem, SourceTheoremError> {
    let module = module().map_err(SourceTheoremError::ModuleParseFailed)?;

    super::proof::source_theorem_result(module, name, super::computation_theory())
}

pub fn reverse_call(value: Computation) -> Computation {
    apply(reverse(), value)
}

pub fn reverse_acc_call(list: Computation, acc: Computation) -> Computation {
    apply(apply(reverse_acc(), list), acc)
}

pub fn append_call(left: Computation, right: Computation) -> Computation {
    apply(apply(append(), left), right)
}

/// If `list` and `acc` are lists, then `reverse_acc(list, acc)` computes to a list.
///
/// `result` names the existential result in `computes_to_list` and should be
/// distinct from `list` and `acc`.
pub fn reverse_acc_computes_to_list_theorem(list: Symbol, acc: Symbol, result: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        forall_where(
            acc,
            is_list(var(acc)),
            computes_to_list(result, reverse_acc_call(var(list), var(acc))),
        ),
    )
}

/// If `list` is a list, then `reverse(list)` computes to a list.
///
/// `result` names the existential result in `computes_to_list` and should be
/// distinct from `list`.
pub fn reverse_computes_to_list_theorem(list: Symbol, result: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to_list(result, reverse_call(var(list))),
    )
}

/// If `right` is a list, then `append(nil, right)` computes to a list.
pub fn append_nil_computes_to_list_theorem(right: Symbol, result: Symbol) -> Prop {
    forall_where(
        right,
        is_list(var(right)),
        computes_to_list(result, append_call(nil(), var(right))),
    )
}

/// If `left` and `right` are lists, then `append(left, right)` computes to a list.
pub fn append_computes_to_list_theorem(left: Symbol, right: Symbol, result: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        forall_where(
            right,
            is_list(var(right)),
            computes_to_list(result, append_call(var(left), var(right))),
        ),
    )
}

/// Appending to `nil` on the left returns the right list exactly.
pub fn append_nil_returns_right_theorem(right: Symbol) -> Prop {
    forall_where(
        right,
        is_list(var(right)),
        computes_to(append_call(nil(), var(right)), var(right)),
    )
}

/// Appending `nil` on the right returns the left list exactly.
pub fn append_right_nil_theorem(left: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        computes_to(append_call(var(left), nil()), var(left)),
    )
}

/// Appending a cons list peels one element from the left.
pub fn append_cons_theorem(head: Symbol, tail: Symbol, right: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            forall_where(
                right,
                is_list(var(right)),
                computes_to(
                    append_call(cons(var(head), var(tail)), var(right)),
                    cons(var(head), append_call(var(tail), var(right))),
                ),
            ),
        ),
    )
}

/// Appending a singleton list conses its only element onto the right list.
pub fn append_singleton_theorem(head: Symbol, right: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            right,
            is_list(var(right)),
            computes_to(
                append_call(singleton(var(head)), var(right)),
                cons(var(head), var(right)),
            ),
        ),
    )
}

/// Appending lists is associative.
pub fn append_assoc_theorem(left: Symbol, middle: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        forall_where(
            middle,
            is_list(var(middle)),
            forall_where(
                right,
                is_list(var(right)),
                computes_to(
                    append_call(append_call(var(left), var(middle)), var(right)),
                    append_call(var(left), append_call(var(middle), var(right))),
                ),
            ),
        ),
    )
}

/// A function whose result is the denotational divergence marker.
pub fn loop_forever() -> Computation {
    lambda(LOOP_ARGUMENT, Computation::Diverge)
}

pub fn loop_forever_call() -> Computation {
    apply(loop_forever(), unit())
}

/// Build the concrete evaluator path using the prelude definitions.
pub fn evaluation_chain(
    computation: Computation,
    limit: usize,
) -> Result<Vec<Computation>, EvaluationProofError> {
    let theory = super::computation_theory();
    evaluation_chain_in_theory(computation, &theory, limit)
}

pub fn evaluation_chain_in_theory(
    computation: Computation,
    theory: &Theory,
    limit: usize,
) -> Result<Vec<Computation>, EvaluationProofError> {
    super::proof::evaluation_chain_in_theory(computation, theory, limit)
}

/// A small tactic that turns bounded evaluation into a `Proof::Steps` object.
///
/// This uses the prelude computation theory. Use `proof_by_evaluation_in_theory`
/// for a custom theory.
pub fn proof_by_evaluation(
    computation: Computation,
    expected: impl Into<Outcome>,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let theory = super::computation_theory();
    proof_by_evaluation_in_theory(computation, expected, &theory, limit)
}

pub fn proof_by_evaluation_in_theory(
    computation: Computation,
    expected: impl Into<Outcome>,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    super::proof::proof_by_evaluation_in_theory(computation, expected, theory, limit)
}

pub fn proof_by_reduction_in_theory(
    computation: Computation,
    expected: impl Into<Outcome>,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    super::proof::proof_by_reduction_in_theory(computation, expected, theory, limit)
}

pub fn proof_by_same_normal_form_in_theory(
    left: Computation,
    right: Computation,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    super::proof::proof_by_same_normal_form_in_theory(left, right, theory, limit)
}

pub fn check_evaluates_to(
    computation: Computation,
    outcome: impl Into<Outcome>,
    proof: &Proof,
) -> bool {
    let theory = super::computation_theory();
    check_evaluates_to_in_theory(computation, outcome, proof, &theory)
}

pub fn check_evaluates_to_in_theory(
    computation: Computation,
    outcome: impl Into<Outcome>,
    proof: &Proof,
    theory: &Theory,
) -> bool {
    super::proof::check_evaluates_to_in_theory(computation, outcome, proof, theory)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Effect, Proof, RUNTIME_ERROR, Value, computes_to, diverges, exists_where};

    const A: Symbol = Symbol(100);
    const B: Symbol = Symbol(101);
    const NOT_A_LIST: Symbol = Symbol(102);
    const X: Symbol = Symbol(200);
    const ACCUMULATOR: Symbol = Symbol(201);
    const RESULT: Symbol = Symbol(202);
    const HEAD: Symbol = Symbol(203);
    const TAIL: Symbol = Symbol(204);
    const RIGHT_LIST: Symbol = Symbol(205);

    fn prove_evaluation(computation: Computation, expected: impl Into<Outcome>) -> Proof {
        proof_by_evaluation(computation, expected, 512).expect("example should evaluate")
    }

    fn assert_evaluates(computation: Computation, expected: impl Into<Outcome>) {
        let expected = expected.into();
        let proof = prove_evaluation(computation.clone(), expected.clone());
        assert!(check_evaluates_to(computation, expected, &proof));
    }

    fn value(computation: Computation) -> Value {
        computation
            .as_value()
            .expect("expected a value computation")
    }

    #[test]
    fn reverse_acc_computes_to_list_theorem_has_expected_shape() {
        assert_eq!(
            reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
            forall_where(
                X,
                is_list(var(X)),
                forall_where(
                    ACCUMULATOR,
                    is_list(var(ACCUMULATOR)),
                    exists_where(
                        RESULT,
                        is_list(var(RESULT)),
                        computes_to(reverse_acc_call(var(X), var(ACCUMULATOR)), var(RESULT)),
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
            forall_where(
                X,
                is_list(var(X)),
                exists_where(
                    RESULT,
                    is_list(var(RESULT)),
                    computes_to(reverse_call(var(X)), var(RESULT)),
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
            forall_where(
                X,
                is_list(var(X)),
                exists_where(
                    RESULT,
                    is_list(var(RESULT)),
                    computes_to(append_call(nil(), var(X)), var(RESULT)),
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
    fn append_computes_to_list_theorem_has_expected_shape() {
        let appended = append_call(var(X), var(ACCUMULATOR));
        let right_case = exists_where(
            RESULT,
            is_list(var(RESULT)),
            computes_to(appended, var(RESULT)),
        );
        let left_case = forall_where(ACCUMULATOR, is_list(var(ACCUMULATOR)), right_case);

        assert_eq!(
            append_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
            forall_where(X, is_list(var(X)), left_case)
        );
    }

    #[test]
    fn append_source_theorem_has_expected_shape() {
        let left = theorem_symbol(APPEND_COMPUTES_TO_LIST, "left");
        let right = theorem_symbol(APPEND_COMPUTES_TO_LIST, "right");
        let result = theorem_symbol(APPEND_COMPUTES_TO_LIST, "result");

        assert_eq!(
            append_computes_to_list_source_theorem(),
            append_computes_to_list_theorem(left, right, result)
        );
    }

    #[test]
    fn append_nil_returns_right_source_theorem_has_expected_shape() {
        let right = theorem_symbol(APPEND_NIL_RETURNS_RIGHT, "right");

        assert_eq!(
            append_nil_returns_right_source_theorem(),
            append_nil_returns_right_theorem(right)
        );
    }

    #[test]
    fn append_right_nil_source_theorem_has_expected_shape() {
        let left = theorem_symbol(APPEND_RIGHT_NIL, "left");

        assert_eq!(
            append_right_nil_source_theorem(),
            append_right_nil_theorem(left)
        );
    }

    #[test]
    fn append_cons_theorem_has_expected_shape() {
        assert_eq!(
            append_cons_theorem(HEAD, TAIL, RIGHT_LIST),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    forall_where(
                        RIGHT_LIST,
                        is_list(var(RIGHT_LIST)),
                        computes_to(
                            append_call(cons(var(HEAD), var(TAIL)), var(RIGHT_LIST)),
                            cons(var(HEAD), append_call(var(TAIL), var(RIGHT_LIST))),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn append_cons_source_theorem_has_expected_shape() {
        let head = theorem_symbol(APPEND_CONS, "head");
        let tail = theorem_symbol(APPEND_CONS, "tail");
        let right = theorem_symbol(APPEND_CONS, "right");

        assert_eq!(
            append_cons_source_theorem(),
            append_cons_theorem(head, tail, right)
        );
    }

    #[test]
    fn append_singleton_theorem_has_expected_shape() {
        assert_eq!(
            append_singleton_theorem(HEAD, RIGHT_LIST),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    RIGHT_LIST,
                    is_list(var(RIGHT_LIST)),
                    computes_to(
                        append_call(singleton(var(HEAD)), var(RIGHT_LIST)),
                        cons(var(HEAD), var(RIGHT_LIST)),
                    ),
                ),
            )
        );
    }

    #[test]
    fn append_singleton_source_theorem_has_expected_shape() {
        let head = theorem_symbol(APPEND_SINGLETON, "head");
        let right = theorem_symbol(APPEND_SINGLETON, "right");

        assert_eq!(
            append_singleton_source_theorem(),
            append_singleton_theorem(head, right)
        );
    }

    #[test]
    fn append_assoc_theorem_has_expected_shape() {
        assert_eq!(
            append_assoc_theorem(X, ACCUMULATOR, RIGHT_LIST),
            forall_where(
                X,
                is_list(var(X)),
                forall_where(
                    ACCUMULATOR,
                    is_list(var(ACCUMULATOR)),
                    forall_where(
                        RIGHT_LIST,
                        is_list(var(RIGHT_LIST)),
                        computes_to(
                            append_call(append_call(var(X), var(ACCUMULATOR)), var(RIGHT_LIST)),
                            append_call(var(X), append_call(var(ACCUMULATOR), var(RIGHT_LIST))),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn append_assoc_source_theorem_has_expected_shape() {
        let left = theorem_symbol(APPEND_ASSOC, "left");
        let middle = theorem_symbol(APPEND_ASSOC, "middle");
        let right = theorem_symbol(APPEND_ASSOC, "right");

        assert_eq!(
            append_assoc_source_theorem(),
            append_assoc_theorem(left, middle, right)
        );
    }

    #[test]
    fn reverse_source_theorem_uses_source_proof_script() {
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
        assert!(matches!(
            theorem_definition(APPEND_COMPUTES_TO_LIST).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(APPEND_NIL_RETURNS_RIGHT).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(APPEND_RIGHT_NIL).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(APPEND_CONS).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(APPEND_SINGLETON).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(APPEND_ASSOC).proof,
            ProofScript::Proof(_)
        ));
    }

    #[test]
    fn reverse_nil_terminates_without_error() {
        assert_evaluates(reverse_call(nil()), Value::nil());
    }

    #[test]
    fn reverse_singleton_terminates_without_error() {
        let list = singleton(quote(A));

        assert_evaluates(reverse_call(list.clone()), value(list));
    }

    #[test]
    fn reverse_pair_terminates_without_error() {
        assert_evaluates(
            reverse_call(pair(quote(A), quote(B))),
            value(pair(quote(B), quote(A))),
        );
    }

    #[test]
    fn reverse_triple_terminates_without_error() {
        assert_evaluates(
            reverse_call(triple(quote(A), quote(B), quote(NOT_A_LIST))),
            value(triple(quote(NOT_A_LIST), quote(B), quote(A))),
        );
    }

    #[test]
    fn append_nil_returns_right_list() {
        let list = pair(quote(A), quote(B));

        assert_evaluates(append_call(nil(), list.clone()), value(list));
    }

    #[test]
    fn append_pair_terminates_without_error() {
        assert_evaluates(
            append_call(pair(quote(A), quote(B)), singleton(quote(NOT_A_LIST))),
            value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
        );
    }

    #[test]
    fn append_singleton_cons_theorem_example() {
        assert_evaluates(
            append_call(singleton(quote(A)), pair(quote(B), quote(NOT_A_LIST))),
            value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
        );
    }

    #[test]
    fn append_assoc_theorem_example() {
        let left = singleton(quote(A));
        let middle = singleton(quote(B));
        let right = singleton(quote(NOT_A_LIST));
        let expected = triple(quote(A), quote(B), quote(NOT_A_LIST));

        assert_evaluates(
            append_call(append_call(left, middle), right),
            value(expected),
        );
    }

    #[test]
    fn loop_forever_diverges() {
        let theory = crate::prelude::theory();
        let computation = loop_forever_call();
        let proof = prove_evaluation(computation.clone(), Effect::diverge());

        assert!(theory.check(&proof, &diverges(computation)));
    }

    #[test]
    fn reverse_non_list_input_reduces_to_error() {
        assert_evaluates(
            reverse_call(quote(NOT_A_LIST)),
            Effect::error(RUNTIME_ERROR),
        );
    }

    #[test]
    fn reverse_malformed_tail_reduces_to_error() {
        assert_evaluates(
            reverse_call(cons(quote(A), quote(NOT_A_LIST))),
            Effect::error(RUNTIME_ERROR),
        );
    }

    #[test]
    fn evaluation_proof_rejects_wrong_expected_value() {
        assert_eq!(
            proof_by_evaluation(reverse_call(nil()), Value::quote(NOT_A_LIST), 64),
            Err(EvaluationProofError::UnexpectedNormalForm {
                expected: quote(NOT_A_LIST),
                actual: nil(),
            })
        );
    }
}
