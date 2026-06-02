//! List definitions and theorems for the standard prelude.

use crate::{
    Computation, ErrorName, Lambda, ListCase, Name, Outcome, Proof, Prop, RUNTIME_ERROR, Symbol,
    Theorem, Theory, computes_to, computes_to_list,
    elab::{
        proof,
        source::{self, ModuleSpec, ParseError, ParsedModule, ParsedTheorem, SymbolBinding},
    },
    errors_with, forall_where, is_list, is_value,
};

use super::{
    APPEND, APPEND_ASSOC, APPEND_COMPUTES_TO_LIST, APPEND_CONS, APPEND_NIL_COMPUTES_TO_LIST,
    APPEND_NIL_RETURNS_RIGHT, APPEND_RIGHT_NIL, APPEND_SINGLETON, CONCAT, CONCAT_NIL, FALSE, INIT,
    INIT_CONS, INIT_NIL_ERRORS, INIT_SINGLETON, IS_SINGLETON, IS_SINGLETON_CONS, IS_SINGLETON_NIL,
    IS_SINGLETON_SINGLETON, LAST, LAST_CONS, LAST_NIL_ERRORS, LAST_SINGLETON, NULL, NULL_CONS,
    NULL_NIL, REVERSE, REVERSE_ACC, REVERSE_ACC_APPEND, REVERSE_ACC_COMPUTES_TO_LIST,
    REVERSE_ACC_OF_APPEND, REVERSE_ACC_REVERSE, REVERSE_APPEND, REVERSE_COMPUTES_TO_LIST,
    REVERSE_CONS, REVERSE_DOUBLE, REVERSE_NIL, REVERSE_NIL_COMPUTES_TO_LIST, REVERSE_SINGLETON,
    SNOC, SNOC_COMPUTES_TO_LIST, SNOC_CONS, SNOC_NIL, SourceTheoremError, TRUE,
};

pub use crate::elab::EvaluationProofError;

#[cfg(test)]
use crate::elab::source::ProofScript;

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
const VALUE: Symbol = Symbol(1_010);
const LISTS: Symbol = Symbol(1_011);
const REST_CELL: Symbol = Symbol(1_012);

pub(super) const MODULE: ModuleSpec = ModuleSpec {
    source: SOURCE,
    computation_definitions: &[
        source::NameBinding {
            spelling: "reverse_acc",
            name: REVERSE_ACC,
        },
        source::NameBinding {
            spelling: "reverse",
            name: REVERSE,
        },
        source::NameBinding {
            spelling: "append",
            name: APPEND,
        },
        source::NameBinding {
            spelling: "snoc",
            name: SNOC,
        },
        source::NameBinding {
            spelling: "concat",
            name: CONCAT,
        },
        source::NameBinding {
            spelling: "last",
            name: LAST,
        },
        source::NameBinding {
            spelling: "init",
            name: INIT,
        },
        source::NameBinding {
            spelling: "null",
            name: NULL,
        },
        source::NameBinding {
            spelling: "is-singleton",
            name: IS_SINGLETON,
        },
    ],
    theorem_definitions: &[
        source::NameBinding {
            spelling: "reverse_acc_computes_to_list",
            name: REVERSE_ACC_COMPUTES_TO_LIST,
        },
        source::NameBinding {
            spelling: "reverse_computes_to_list",
            name: REVERSE_COMPUTES_TO_LIST,
        },
        source::NameBinding {
            spelling: "reverse_nil_computes_to_list",
            name: REVERSE_NIL_COMPUTES_TO_LIST,
        },
        source::NameBinding {
            spelling: "reverse_nil",
            name: REVERSE_NIL,
        },
        source::NameBinding {
            spelling: "reverse_singleton",
            name: REVERSE_SINGLETON,
        },
        source::NameBinding {
            spelling: "reverse_acc_append",
            name: REVERSE_ACC_APPEND,
        },
        source::NameBinding {
            spelling: "reverse_cons",
            name: REVERSE_CONS,
        },
        source::NameBinding {
            spelling: "reverse_acc_reverse",
            name: REVERSE_ACC_REVERSE,
        },
        source::NameBinding {
            spelling: "reverse_double",
            name: REVERSE_DOUBLE,
        },
        source::NameBinding {
            spelling: "reverse_acc_of_append",
            name: REVERSE_ACC_OF_APPEND,
        },
        source::NameBinding {
            spelling: "reverse_append",
            name: REVERSE_APPEND,
        },
        source::NameBinding {
            spelling: "snoc_computes_to_list",
            name: SNOC_COMPUTES_TO_LIST,
        },
        source::NameBinding {
            spelling: "snoc_nil",
            name: SNOC_NIL,
        },
        source::NameBinding {
            spelling: "snoc_cons",
            name: SNOC_CONS,
        },
        source::NameBinding {
            spelling: "concat_nil",
            name: CONCAT_NIL,
        },
        source::NameBinding {
            spelling: "last_nil_errors",
            name: LAST_NIL_ERRORS,
        },
        source::NameBinding {
            spelling: "last_singleton",
            name: LAST_SINGLETON,
        },
        source::NameBinding {
            spelling: "last_cons",
            name: LAST_CONS,
        },
        source::NameBinding {
            spelling: "init_nil_errors",
            name: INIT_NIL_ERRORS,
        },
        source::NameBinding {
            spelling: "init_singleton",
            name: INIT_SINGLETON,
        },
        source::NameBinding {
            spelling: "init_cons",
            name: INIT_CONS,
        },
        source::NameBinding {
            spelling: "null_nil",
            name: NULL_NIL,
        },
        source::NameBinding {
            spelling: "null_cons",
            name: NULL_CONS,
        },
        source::NameBinding {
            spelling: "is_singleton_nil",
            name: IS_SINGLETON_NIL,
        },
        source::NameBinding {
            spelling: "is_singleton_singleton",
            name: IS_SINGLETON_SINGLETON,
        },
        source::NameBinding {
            spelling: "is_singleton_cons",
            name: IS_SINGLETON_CONS,
        },
        source::NameBinding {
            spelling: "append_nil_computes_to_list",
            name: APPEND_NIL_COMPUTES_TO_LIST,
        },
        source::NameBinding {
            spelling: "append_computes_to_list",
            name: APPEND_COMPUTES_TO_LIST,
        },
        source::NameBinding {
            spelling: "append_nil_returns_right",
            name: APPEND_NIL_RETURNS_RIGHT,
        },
        source::NameBinding {
            spelling: "append_right_nil",
            name: APPEND_RIGHT_NIL,
        },
        source::NameBinding {
            spelling: "append_cons",
            name: APPEND_CONS,
        },
        source::NameBinding {
            spelling: "append_singleton",
            name: APPEND_SINGLETON,
        },
        source::NameBinding {
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
            spelling: ":true",
            symbol: TRUE,
        },
        SymbolBinding {
            spelling: ":false",
            symbol: FALSE,
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
        SymbolBinding {
            spelling: "value",
            symbol: VALUE,
        },
        SymbolBinding {
            spelling: "lists",
            symbol: LISTS,
        },
        SymbolBinding {
            spelling: "rest_cell",
            symbol: REST_CELL,
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

pub fn true_value() -> Computation {
    quote(TRUE)
}

pub fn false_value() -> Computation {
    quote(FALSE)
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

pub fn snoc() -> Computation {
    super::snoc()
}

pub fn snoc_definition() -> Computation {
    definition(SNOC)
}

pub fn concat() -> Computation {
    super::concat()
}

pub fn concat_definition() -> Computation {
    definition(CONCAT)
}

pub fn last() -> Computation {
    super::last()
}

pub fn last_definition() -> Computation {
    definition(LAST)
}

pub fn init() -> Computation {
    super::init()
}

pub fn init_definition() -> Computation {
    definition(INIT)
}

pub fn null() -> Computation {
    super::null()
}

pub fn null_definition() -> Computation {
    definition(NULL)
}

pub fn is_singleton() -> Computation {
    super::is_singleton()
}

pub fn is_singleton_definition() -> Computation {
    definition(IS_SINGLETON)
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

pub fn reverse_nil_source_theorem() -> Prop {
    theorem_prop(REVERSE_NIL)
}

pub fn reverse_singleton_source_theorem() -> Prop {
    theorem_prop(REVERSE_SINGLETON)
}

pub fn reverse_acc_append_source_theorem() -> Prop {
    theorem_prop(REVERSE_ACC_APPEND)
}

pub fn reverse_cons_source_theorem() -> Prop {
    theorem_prop(REVERSE_CONS)
}

pub fn reverse_acc_reverse_source_theorem() -> Prop {
    theorem_prop(REVERSE_ACC_REVERSE)
}

pub fn reverse_double_source_theorem() -> Prop {
    theorem_prop(REVERSE_DOUBLE)
}

pub fn reverse_acc_of_append_source_theorem() -> Prop {
    theorem_prop(REVERSE_ACC_OF_APPEND)
}

pub fn reverse_append_source_theorem() -> Prop {
    theorem_prop(REVERSE_APPEND)
}

pub fn snoc_computes_to_list_source_theorem() -> Prop {
    theorem_prop(SNOC_COMPUTES_TO_LIST)
}

pub fn snoc_nil_source_theorem() -> Prop {
    theorem_prop(SNOC_NIL)
}

pub fn snoc_cons_source_theorem() -> Prop {
    theorem_prop(SNOC_CONS)
}

pub fn concat_nil_source_theorem() -> Prop {
    theorem_prop(CONCAT_NIL)
}

pub fn last_nil_errors_source_theorem() -> Prop {
    theorem_prop(LAST_NIL_ERRORS)
}

pub fn last_singleton_source_theorem() -> Prop {
    theorem_prop(LAST_SINGLETON)
}

pub fn last_cons_source_theorem() -> Prop {
    theorem_prop(LAST_CONS)
}

pub fn init_nil_errors_source_theorem() -> Prop {
    theorem_prop(INIT_NIL_ERRORS)
}

pub fn init_singleton_source_theorem() -> Prop {
    theorem_prop(INIT_SINGLETON)
}

pub fn init_cons_source_theorem() -> Prop {
    theorem_prop(INIT_CONS)
}

pub fn null_nil_source_theorem() -> Prop {
    theorem_prop(NULL_NIL)
}

pub fn null_cons_source_theorem() -> Prop {
    theorem_prop(NULL_CONS)
}

pub fn is_singleton_nil_source_theorem() -> Prop {
    theorem_prop(IS_SINGLETON_NIL)
}

pub fn is_singleton_singleton_source_theorem() -> Prop {
    theorem_prop(IS_SINGLETON_SINGLETON)
}

pub fn is_singleton_cons_source_theorem() -> Prop {
    theorem_prop(IS_SINGLETON_CONS)
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

    proof::source_theorem_result(module, name, super::computation_theory())
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

pub fn snoc_call(list: Computation, value: Computation) -> Computation {
    apply(apply(snoc(), list), value)
}

pub fn concat_call(lists: Computation) -> Computation {
    apply(concat(), lists)
}

pub fn last_call(list: Computation) -> Computation {
    apply(last(), list)
}

pub fn init_call(list: Computation) -> Computation {
    apply(init(), list)
}

pub fn null_call(list: Computation) -> Computation {
    apply(null(), list)
}

pub fn is_singleton_call(list: Computation) -> Computation {
    apply(is_singleton(), list)
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

/// Reversing `nil` returns `nil`.
pub fn reverse_nil_theorem() -> Prop {
    computes_to(reverse_call(nil()), nil())
}

/// Reversing a singleton list returns the same singleton list.
pub fn reverse_singleton_theorem(head: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        computes_to(reverse_call(singleton(var(head))), singleton(var(head))),
    )
}

/// Reversal with an accumulator is equivalent to appending the accumulator to the
/// ordinary reverse.
pub fn reverse_acc_append_theorem(list: Symbol, acc: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        forall_where(
            acc,
            is_list(var(acc)),
            computes_to(
                reverse_acc_call(var(list), var(acc)),
                append_call(reverse_call(var(list)), var(acc)),
            ),
        ),
    )
}

/// Reversing a cons appends the head onto the reversed tail.
pub fn reverse_cons_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            computes_to(
                reverse_call(cons(var(head), var(tail))),
                append_call(reverse_call(var(tail)), singleton(var(head))),
            ),
        ),
    )
}

/// Reversing an accumulated reverse appends the original list after the reversed
/// accumulator.
pub fn reverse_acc_reverse_theorem(list: Symbol, acc: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        forall_where(
            acc,
            is_list(var(acc)),
            computes_to(
                reverse_call(reverse_acc_call(var(list), var(acc))),
                append_call(reverse_call(var(acc)), var(list)),
            ),
        ),
    )
}

/// Reversing a list twice returns the original list.
pub fn reverse_double_theorem(list: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to(reverse_call(reverse_call(var(list))), var(list)),
    )
}

/// Reversing over an appended input moves the left side into the accumulator.
pub fn reverse_acc_of_append_theorem(left: Symbol, right: Symbol, acc: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        forall_where(
            right,
            is_list(var(right)),
            forall_where(
                acc,
                is_list(var(acc)),
                computes_to(
                    reverse_acc_call(append_call(var(left), var(right)), var(acc)),
                    reverse_acc_call(var(right), reverse_acc_call(var(left), var(acc))),
                ),
            ),
        ),
    )
}

/// Reversing an append swaps the sides and reverses both.
pub fn reverse_append_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        forall_where(
            right,
            is_list(var(right)),
            computes_to(
                reverse_call(append_call(var(left), var(right))),
                append_call(reverse_call(var(right)), reverse_call(var(left))),
            ),
        ),
    )
}

/// Adding one value to the end of a list returns a list.
pub fn snoc_computes_to_list_theorem(list: Symbol, value: Symbol, result: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        forall_where(
            value,
            is_value(var(value)),
            computes_to_list(result, snoc_call(var(list), var(value))),
        ),
    )
}

/// Adding a value to the end of `nil` returns a singleton.
pub fn snoc_nil_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        computes_to(snoc_call(nil(), var(value)), singleton(var(value))),
    )
}

/// Adding a value to the end of a cons preserves the head.
pub fn snoc_cons_theorem(head: Symbol, tail: Symbol, value: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            forall_where(
                value,
                is_value(var(value)),
                computes_to(
                    snoc_call(cons(var(head), var(tail)), var(value)),
                    cons(var(head), snoc_call(var(tail), var(value))),
                ),
            ),
        ),
    )
}

/// Concatenating no lists returns `nil`.
pub fn concat_nil_theorem() -> Prop {
    computes_to(concat_call(nil()), nil())
}

/// `last(nil)` errors.
pub fn last_nil_errors_theorem() -> Prop {
    errors_with(last_call(nil()), RUNTIME_ERROR)
}

/// The last element of a singleton is its only element.
pub fn last_singleton_theorem(head: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        computes_to(last_call(singleton(var(head))), var(head)),
    )
}

/// The last element of a list with at least two elements is the last element of
/// its tail.
pub fn last_cons_theorem(head: Symbol, next: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            next,
            is_value(var(next)),
            forall_where(
                tail,
                is_list(var(tail)),
                computes_to(
                    last_call(cons(var(head), cons(var(next), var(tail)))),
                    last_call(cons(var(next), var(tail))),
                ),
            ),
        ),
    )
}

/// `init(nil)` errors.
pub fn init_nil_errors_theorem() -> Prop {
    errors_with(init_call(nil()), RUNTIME_ERROR)
}

/// The init of a singleton is `nil`.
pub fn init_singleton_theorem(head: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        computes_to(init_call(singleton(var(head))), nil()),
    )
}

/// The init of a list with at least two elements preserves the head and recurs
/// into the tail.
pub fn init_cons_theorem(head: Symbol, next: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            next,
            is_value(var(next)),
            forall_where(
                tail,
                is_list(var(tail)),
                computes_to(
                    init_call(cons(var(head), cons(var(next), var(tail)))),
                    cons(var(head), init_call(cons(var(next), var(tail)))),
                ),
            ),
        ),
    )
}

/// `null(nil)` returns `:true`.
pub fn null_nil_theorem() -> Prop {
    computes_to(null_call(nil()), true_value())
}

/// `null` returns `:false` for every cons.
pub fn null_cons_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            computes_to(null_call(cons(var(head), var(tail))), false_value()),
        ),
    )
}

/// `is-singleton(nil)` returns `:false`.
pub fn is_singleton_nil_theorem() -> Prop {
    computes_to(is_singleton_call(nil()), false_value())
}

/// `is-singleton` returns `:true` for a one-element list.
pub fn is_singleton_singleton_theorem(head: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        computes_to(is_singleton_call(singleton(var(head))), true_value()),
    )
}

/// `is-singleton` returns `:false` for lists with at least two elements.
pub fn is_singleton_cons_theorem(head: Symbol, next: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            next,
            is_value(var(next)),
            forall_where(
                tail,
                is_list(var(tail)),
                computes_to(
                    is_singleton_call(cons(var(head), cons(var(next), var(tail)))),
                    false_value(),
                ),
            ),
        ),
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
    proof::evaluation_chain_in_theory(computation, theory, limit)
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
    proof::proof_by_evaluation_in_theory(computation, expected, theory, limit)
}

pub fn proof_by_reduction_in_theory(
    computation: Computation,
    expected: impl Into<Outcome>,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    proof::proof_by_reduction_in_theory(computation, expected, theory, limit)
}

pub fn proof_by_same_normal_form_in_theory(
    left: Computation,
    right: Computation,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    proof::proof_by_same_normal_form_in_theory(left, right, theory, limit)
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
    proof::check_evaluates_to_in_theory(computation, outcome, proof, theory)
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
    const NEXT: Symbol = Symbol(206);

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
    fn reverse_nil_exact_source_theorem_has_expected_shape() {
        assert_eq!(reverse_nil_source_theorem(), reverse_nil_theorem());
    }

    #[test]
    fn reverse_singleton_theorem_has_expected_shape() {
        assert_eq!(
            reverse_singleton_theorem(HEAD),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                computes_to(reverse_call(singleton(var(HEAD))), singleton(var(HEAD))),
            )
        );
    }

    #[test]
    fn reverse_singleton_source_theorem_has_expected_shape() {
        let head = theorem_symbol(REVERSE_SINGLETON, "head");

        assert_eq!(
            reverse_singleton_source_theorem(),
            reverse_singleton_theorem(head)
        );
    }

    #[test]
    fn reverse_acc_append_theorem_has_expected_shape() {
        assert_eq!(
            reverse_acc_append_theorem(X, ACCUMULATOR),
            forall_where(
                X,
                is_list(var(X)),
                forall_where(
                    ACCUMULATOR,
                    is_list(var(ACCUMULATOR)),
                    computes_to(
                        reverse_acc_call(var(X), var(ACCUMULATOR)),
                        append_call(reverse_call(var(X)), var(ACCUMULATOR)),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_acc_append_source_theorem_has_expected_shape() {
        let list = theorem_symbol(REVERSE_ACC_APPEND, "list");
        let acc = theorem_symbol(REVERSE_ACC_APPEND, "acc");

        assert_eq!(
            reverse_acc_append_source_theorem(),
            reverse_acc_append_theorem(list, acc)
        );
    }

    #[test]
    fn reverse_cons_theorem_has_expected_shape() {
        assert_eq!(
            reverse_cons_theorem(HEAD, TAIL),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    computes_to(
                        reverse_call(cons(var(HEAD), var(TAIL))),
                        append_call(reverse_call(var(TAIL)), singleton(var(HEAD))),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_cons_source_theorem_has_expected_shape() {
        let head = theorem_symbol(REVERSE_CONS, "head");
        let tail = theorem_symbol(REVERSE_CONS, "tail");

        assert_eq!(
            reverse_cons_source_theorem(),
            reverse_cons_theorem(head, tail)
        );
    }

    #[test]
    fn reverse_acc_reverse_theorem_has_expected_shape() {
        assert_eq!(
            reverse_acc_reverse_theorem(X, ACCUMULATOR),
            forall_where(
                X,
                is_list(var(X)),
                forall_where(
                    ACCUMULATOR,
                    is_list(var(ACCUMULATOR)),
                    computes_to(
                        reverse_call(reverse_acc_call(var(X), var(ACCUMULATOR))),
                        append_call(reverse_call(var(ACCUMULATOR)), var(X)),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_acc_reverse_source_theorem_has_expected_shape() {
        let list = theorem_symbol(REVERSE_ACC_REVERSE, "list");
        let acc = theorem_symbol(REVERSE_ACC_REVERSE, "acc");

        assert_eq!(
            reverse_acc_reverse_source_theorem(),
            reverse_acc_reverse_theorem(list, acc)
        );
    }

    #[test]
    fn reverse_double_theorem_has_expected_shape() {
        assert_eq!(
            reverse_double_theorem(X),
            forall_where(
                X,
                is_list(var(X)),
                computes_to(reverse_call(reverse_call(var(X))), var(X)),
            )
        );
    }

    #[test]
    fn reverse_double_source_theorem_has_expected_shape() {
        let list = theorem_symbol(REVERSE_DOUBLE, "list");

        assert_eq!(
            reverse_double_source_theorem(),
            reverse_double_theorem(list)
        );
    }

    #[test]
    fn reverse_acc_of_append_theorem_has_expected_shape() {
        assert_eq!(
            reverse_acc_of_append_theorem(X, RIGHT_LIST, ACCUMULATOR),
            forall_where(
                X,
                is_list(var(X)),
                forall_where(
                    RIGHT_LIST,
                    is_list(var(RIGHT_LIST)),
                    forall_where(
                        ACCUMULATOR,
                        is_list(var(ACCUMULATOR)),
                        computes_to(
                            reverse_acc_call(
                                append_call(var(X), var(RIGHT_LIST)),
                                var(ACCUMULATOR),
                            ),
                            reverse_acc_call(
                                var(RIGHT_LIST),
                                reverse_acc_call(var(X), var(ACCUMULATOR)),
                            ),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_acc_of_append_source_theorem_has_expected_shape() {
        let left = theorem_symbol(REVERSE_ACC_OF_APPEND, "left");
        let right = theorem_symbol(REVERSE_ACC_OF_APPEND, "right");
        let acc = theorem_symbol(REVERSE_ACC_OF_APPEND, "acc");

        assert_eq!(
            reverse_acc_of_append_source_theorem(),
            reverse_acc_of_append_theorem(left, right, acc)
        );
    }

    #[test]
    fn reverse_append_theorem_has_expected_shape() {
        assert_eq!(
            reverse_append_theorem(X, RIGHT_LIST),
            forall_where(
                X,
                is_list(var(X)),
                forall_where(
                    RIGHT_LIST,
                    is_list(var(RIGHT_LIST)),
                    computes_to(
                        reverse_call(append_call(var(X), var(RIGHT_LIST))),
                        append_call(reverse_call(var(RIGHT_LIST)), reverse_call(var(X))),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_append_source_theorem_has_expected_shape() {
        let left = theorem_symbol(REVERSE_APPEND, "left");
        let right = theorem_symbol(REVERSE_APPEND, "right");

        assert_eq!(
            reverse_append_source_theorem(),
            reverse_append_theorem(left, right)
        );
    }

    #[test]
    fn snoc_computes_to_list_theorem_has_expected_shape() {
        assert_eq!(
            snoc_computes_to_list_theorem(X, HEAD, RESULT),
            forall_where(
                X,
                is_list(var(X)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    exists_where(
                        RESULT,
                        is_list(var(RESULT)),
                        computes_to(snoc_call(var(X), var(HEAD)), var(RESULT)),
                    ),
                ),
            )
        );
    }

    #[test]
    fn snoc_source_theorem_has_expected_shape() {
        let list = theorem_symbol(SNOC_COMPUTES_TO_LIST, "list");
        let value = theorem_symbol(SNOC_COMPUTES_TO_LIST, "value");
        let result = theorem_symbol(SNOC_COMPUTES_TO_LIST, "result");

        assert_eq!(
            snoc_computes_to_list_source_theorem(),
            snoc_computes_to_list_theorem(list, value, result)
        );
    }

    #[test]
    fn snoc_exact_theorems_have_expected_shape() {
        assert_eq!(snoc_nil_theorem(HEAD), {
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                computes_to(snoc_call(nil(), var(HEAD)), singleton(var(HEAD))),
            )
        });
        assert_eq!(
            snoc_cons_theorem(HEAD, TAIL, NEXT),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    forall_where(
                        NEXT,
                        is_value(var(NEXT)),
                        computes_to(
                            snoc_call(cons(var(HEAD), var(TAIL)), var(NEXT)),
                            cons(var(HEAD), snoc_call(var(TAIL), var(NEXT))),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn snoc_exact_source_theorems_have_expected_shape() {
        let nil_value = theorem_symbol(SNOC_NIL, "value");
        let cons_head = theorem_symbol(SNOC_CONS, "head");
        let cons_tail = theorem_symbol(SNOC_CONS, "tail");
        let cons_value = theorem_symbol(SNOC_CONS, "value");

        assert_eq!(snoc_nil_source_theorem(), snoc_nil_theorem(nil_value));
        assert_eq!(
            snoc_cons_source_theorem(),
            snoc_cons_theorem(cons_head, cons_tail, cons_value)
        );
    }

    #[test]
    fn concat_nil_source_theorem_has_expected_shape() {
        assert_eq!(concat_nil_source_theorem(), concat_nil_theorem());
    }

    #[test]
    fn last_theorems_have_expected_shape() {
        assert_eq!(
            last_nil_errors_theorem(),
            errors_with(last_call(nil()), RUNTIME_ERROR)
        );
        assert_eq!(
            last_singleton_theorem(HEAD),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                computes_to(last_call(singleton(var(HEAD))), var(HEAD)),
            )
        );
        assert_eq!(
            last_cons_theorem(HEAD, NEXT, TAIL),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    NEXT,
                    is_value(var(NEXT)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            last_call(cons(var(HEAD), cons(var(NEXT), var(TAIL)))),
                            last_call(cons(var(NEXT), var(TAIL))),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn last_source_theorems_have_expected_shape() {
        let singleton_head = theorem_symbol(LAST_SINGLETON, "head");
        let cons_head = theorem_symbol(LAST_CONS, "head");
        let cons_next = theorem_symbol(LAST_CONS, "next");
        let cons_tail = theorem_symbol(LAST_CONS, "tail");

        assert_eq!(last_nil_errors_source_theorem(), last_nil_errors_theorem());
        assert_eq!(
            last_singleton_source_theorem(),
            last_singleton_theorem(singleton_head)
        );
        assert_eq!(
            last_cons_source_theorem(),
            last_cons_theorem(cons_head, cons_next, cons_tail)
        );
    }

    #[test]
    fn init_theorems_have_expected_shape() {
        assert_eq!(
            init_nil_errors_theorem(),
            errors_with(init_call(nil()), RUNTIME_ERROR)
        );
        assert_eq!(
            init_singleton_theorem(HEAD),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                computes_to(init_call(singleton(var(HEAD))), nil()),
            )
        );
        assert_eq!(
            init_cons_theorem(HEAD, NEXT, TAIL),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    NEXT,
                    is_value(var(NEXT)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            init_call(cons(var(HEAD), cons(var(NEXT), var(TAIL)))),
                            cons(var(HEAD), init_call(cons(var(NEXT), var(TAIL)))),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn init_source_theorems_have_expected_shape() {
        let singleton_head = theorem_symbol(INIT_SINGLETON, "head");
        let cons_head = theorem_symbol(INIT_CONS, "head");
        let cons_next = theorem_symbol(INIT_CONS, "next");
        let cons_tail = theorem_symbol(INIT_CONS, "tail");

        assert_eq!(init_nil_errors_source_theorem(), init_nil_errors_theorem());
        assert_eq!(
            init_singleton_source_theorem(),
            init_singleton_theorem(singleton_head)
        );
        assert_eq!(
            init_cons_source_theorem(),
            init_cons_theorem(cons_head, cons_next, cons_tail)
        );
    }

    #[test]
    fn null_theorems_have_expected_shape() {
        assert_eq!(
            null_nil_theorem(),
            computes_to(null_call(nil()), true_value())
        );
        assert_eq!(
            null_cons_theorem(HEAD, TAIL),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    computes_to(null_call(cons(var(HEAD), var(TAIL))), false_value()),
                ),
            )
        );
    }

    #[test]
    fn null_source_theorems_have_expected_shape() {
        let cons_head = theorem_symbol(NULL_CONS, "head");
        let cons_tail = theorem_symbol(NULL_CONS, "tail");

        assert_eq!(null_nil_source_theorem(), null_nil_theorem());
        assert_eq!(
            null_cons_source_theorem(),
            null_cons_theorem(cons_head, cons_tail)
        );
    }

    #[test]
    fn is_singleton_theorems_have_expected_shape() {
        assert_eq!(
            is_singleton_nil_theorem(),
            computes_to(is_singleton_call(nil()), false_value())
        );
        assert_eq!(
            is_singleton_singleton_theorem(HEAD),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                computes_to(is_singleton_call(singleton(var(HEAD))), true_value()),
            )
        );
        assert_eq!(
            is_singleton_cons_theorem(HEAD, NEXT, TAIL),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    NEXT,
                    is_value(var(NEXT)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            is_singleton_call(cons(var(HEAD), cons(var(NEXT), var(TAIL)))),
                            false_value(),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn is_singleton_source_theorems_have_expected_shape() {
        let singleton_head = theorem_symbol(IS_SINGLETON_SINGLETON, "head");
        let cons_head = theorem_symbol(IS_SINGLETON_CONS, "head");
        let cons_next = theorem_symbol(IS_SINGLETON_CONS, "next");
        let cons_tail = theorem_symbol(IS_SINGLETON_CONS, "tail");

        assert_eq!(
            is_singleton_nil_source_theorem(),
            is_singleton_nil_theorem()
        );
        assert_eq!(
            is_singleton_singleton_source_theorem(),
            is_singleton_singleton_theorem(singleton_head)
        );
        assert_eq!(
            is_singleton_cons_source_theorem(),
            is_singleton_cons_theorem(cons_head, cons_next, cons_tail)
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
            theorem_definition(REVERSE_NIL).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_SINGLETON).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_ACC_APPEND).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_CONS).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_ACC_REVERSE).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_DOUBLE).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_ACC_OF_APPEND).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_APPEND).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(SNOC_COMPUTES_TO_LIST).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(SNOC_NIL).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(SNOC_CONS).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(CONCAT_NIL).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(LAST_NIL_ERRORS).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(LAST_SINGLETON).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(LAST_CONS).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(INIT_NIL_ERRORS).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(INIT_SINGLETON).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(INIT_CONS).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(NULL_NIL).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(NULL_CONS).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(IS_SINGLETON_NIL).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(IS_SINGLETON_SINGLETON).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(IS_SINGLETON_CONS).proof,
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
    fn snoc_pair_terminates_without_error() {
        assert_evaluates(
            snoc_call(pair(quote(A), quote(B)), quote(NOT_A_LIST)),
            value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
        );
    }

    #[test]
    fn concat_list_of_lists_terminates_without_error() {
        let lists = pair(singleton(quote(A)), pair(quote(B), quote(NOT_A_LIST)));

        assert_evaluates(
            concat_call(lists),
            value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
        );
    }

    #[test]
    fn last_nil_reduces_to_error() {
        assert_evaluates(last_call(nil()), Effect::error(RUNTIME_ERROR));
    }

    #[test]
    fn last_singleton_returns_value() {
        assert_evaluates(last_call(singleton(quote(A))), Value::quote(A));
    }

    #[test]
    fn last_triple_returns_final_value() {
        assert_evaluates(
            last_call(triple(quote(A), quote(B), quote(NOT_A_LIST))),
            Value::quote(NOT_A_LIST),
        );
    }

    #[test]
    fn init_nil_reduces_to_error() {
        assert_evaluates(init_call(nil()), Effect::error(RUNTIME_ERROR));
    }

    #[test]
    fn init_singleton_returns_nil() {
        assert_evaluates(init_call(singleton(quote(A))), Value::nil());
    }

    #[test]
    fn init_triple_returns_prefix() {
        assert_evaluates(
            init_call(triple(quote(A), quote(B), quote(NOT_A_LIST))),
            value(pair(quote(A), quote(B))),
        );
    }

    #[test]
    fn null_nil_returns_true() {
        assert_evaluates(null_call(nil()), Value::quote(TRUE));
    }

    #[test]
    fn null_cons_returns_false() {
        assert_evaluates(null_call(singleton(quote(A))), Value::quote(FALSE));
    }

    #[test]
    fn is_singleton_nil_returns_false() {
        assert_evaluates(is_singleton_call(nil()), Value::quote(FALSE));
    }

    #[test]
    fn is_singleton_singleton_returns_true() {
        assert_evaluates(is_singleton_call(singleton(quote(A))), Value::quote(TRUE));
    }

    #[test]
    fn is_singleton_pair_returns_false() {
        assert_evaluates(
            is_singleton_call(pair(quote(A), quote(B))),
            Value::quote(FALSE),
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
