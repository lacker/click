//! Test helpers and expected shapes for the list prelude source.

use crate::{
    Computation, Lambda, Outcome, Proof, Prop, RUNTIME_ERROR, Symbol, Theory, computes_to,
    computes_to_list,
    elab::{proof, source::ParsedTheorem},
    errors_with, exists_where, forall_where, implies, is_list, is_value,
};

pub use crate::elab::EvaluationProofError;

const LOOP_ARGUMENT: Symbol = Symbol(1_007);

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

pub fn unit() -> Computation {
    quote(prelude_symbol("unit"))
}

pub fn true_value() -> Computation {
    quote(prelude_symbol(":true"))
}

pub fn false_value() -> Computation {
    quote(prelude_symbol(":false"))
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

fn computation_ref(spelling: &str) -> Computation {
    Computation::Ref(super::computation_name(spelling).expect("prelude should define computation"))
}

pub fn reverse_acc() -> Computation {
    computation_ref("reverse_acc")
}

pub fn reverse_acc_definition() -> Computation {
    definition("reverse_acc")
}

pub fn reverse() -> Computation {
    computation_ref("reverse")
}

pub fn reverse_definition() -> Computation {
    definition("reverse")
}

pub fn append() -> Computation {
    computation_ref("append")
}

pub fn append_definition() -> Computation {
    definition("append")
}

pub fn snoc() -> Computation {
    computation_ref("snoc")
}

pub fn snoc_definition() -> Computation {
    definition("snoc")
}

pub fn concat() -> Computation {
    computation_ref("concat")
}

pub fn concat_definition() -> Computation {
    definition("concat")
}

pub fn map() -> Computation {
    computation_ref("map")
}

pub fn map_definition() -> Computation {
    definition("map")
}

pub fn concat_map() -> Computation {
    computation_ref("concat-map")
}

pub fn concat_map_definition() -> Computation {
    definition("concat-map")
}

pub fn fold_right() -> Computation {
    computation_ref("fold-right")
}

pub fn fold_right_definition() -> Computation {
    definition("fold-right")
}

pub fn fold_left() -> Computation {
    computation_ref("fold-left")
}

pub fn fold_left_definition() -> Computation {
    definition("fold-left")
}

pub fn last() -> Computation {
    computation_ref("last")
}

pub fn last_definition() -> Computation {
    definition("last")
}

pub fn init() -> Computation {
    computation_ref("init")
}

pub fn init_definition() -> Computation {
    definition("init")
}

pub fn null() -> Computation {
    computation_ref("null")
}

pub fn null_definition() -> Computation {
    definition("null")
}

pub fn is_singleton() -> Computation {
    computation_ref("is-singleton")
}

pub fn is_singleton_definition() -> Computation {
    definition("is-singleton")
}

fn definition(spelling: &str) -> Computation {
    let module = super::parsed_list_module().expect("prelude list source should parse");
    let env = super::parsed_prelude_env().expect("prelude source should parse");
    let name = env
        .computation(spelling)
        .expect("prelude list source should define requested computation name");

    module
        .computation(name)
        .cloned()
        .expect("prelude list source should define requested computation")
}

fn prelude_symbol(spelling: &str) -> Symbol {
    super::symbol_name(spelling).expect("prelude source should define requested symbol")
}

pub fn reverse_acc_computes_to_list_source_theorem() -> Prop {
    theorem_prop("reverse_acc_computes_to_list")
}

pub fn reverse_computes_to_list_source_theorem() -> Prop {
    theorem_prop("reverse_computes_to_list")
}

pub fn reverse_nil_computes_to_list_source_theorem() -> Prop {
    theorem_prop("reverse_nil_computes_to_list")
}

pub fn reverse_nil_source_theorem() -> Prop {
    theorem_prop("reverse_nil")
}

pub fn reverse_singleton_source_theorem() -> Prop {
    theorem_prop("reverse_singleton")
}

pub fn reverse_acc_append_source_theorem() -> Prop {
    theorem_prop("reverse_acc_append")
}

pub fn reverse_cons_source_theorem() -> Prop {
    theorem_prop("reverse_cons")
}

pub fn reverse_acc_reverse_source_theorem() -> Prop {
    theorem_prop("reverse_acc_reverse")
}

pub fn reverse_double_source_theorem() -> Prop {
    theorem_prop("reverse_double")
}

pub fn reverse_acc_of_append_source_theorem() -> Prop {
    theorem_prop("reverse_acc_of_append")
}

pub fn reverse_append_source_theorem() -> Prop {
    theorem_prop("reverse_append")
}

pub fn snoc_computes_to_list_source_theorem() -> Prop {
    theorem_prop("snoc_computes_to_list")
}

pub fn snoc_nil_source_theorem() -> Prop {
    theorem_prop("snoc_nil")
}

pub fn snoc_cons_source_theorem() -> Prop {
    theorem_prop("snoc_cons")
}

pub fn concat_nil_source_theorem() -> Prop {
    theorem_prop("concat_nil")
}

pub fn last_nil_errors_source_theorem() -> Prop {
    theorem_prop("last_nil_errors")
}

pub fn last_singleton_source_theorem() -> Prop {
    theorem_prop("last_singleton")
}

pub fn last_cons_source_theorem() -> Prop {
    theorem_prop("last_cons")
}

pub fn init_nil_errors_source_theorem() -> Prop {
    theorem_prop("init_nil_errors")
}

pub fn init_singleton_source_theorem() -> Prop {
    theorem_prop("init_singleton")
}

pub fn init_cons_source_theorem() -> Prop {
    theorem_prop("init_cons")
}

pub fn null_nil_source_theorem() -> Prop {
    theorem_prop("null_nil")
}

pub fn null_cons_source_theorem() -> Prop {
    theorem_prop("null_cons")
}

pub fn is_singleton_nil_source_theorem() -> Prop {
    theorem_prop("is_singleton_nil")
}

pub fn is_singleton_singleton_source_theorem() -> Prop {
    theorem_prop("is_singleton_singleton")
}

pub fn is_singleton_cons_source_theorem() -> Prop {
    theorem_prop("is_singleton_cons")
}

pub fn append_nil_computes_to_list_source_theorem() -> Prop {
    theorem_prop("append_nil_computes_to_list")
}

pub fn append_computes_to_list_source_theorem() -> Prop {
    theorem_prop("append_computes_to_list")
}

pub fn append_nil_returns_right_source_theorem() -> Prop {
    theorem_prop("append_nil_returns_right")
}

pub fn append_right_nil_source_theorem() -> Prop {
    theorem_prop("append_right_nil")
}

pub fn append_cons_source_theorem() -> Prop {
    theorem_prop("append_cons")
}

pub fn append_singleton_source_theorem() -> Prop {
    theorem_prop("append_singleton")
}

pub fn append_assoc_source_theorem() -> Prop {
    theorem_prop("append_assoc")
}

pub fn map_nil_source_theorem() -> Prop {
    theorem_prop("map_nil")
}

pub fn map_cons_source_theorem() -> Prop {
    theorem_prop("map_cons")
}

pub fn map_computes_to_list_source_theorem() -> Prop {
    theorem_prop("map_computes_to_list")
}

pub fn concat_map_nil_source_theorem() -> Prop {
    theorem_prop("concat_map_nil")
}

pub fn concat_map_cons_source_theorem() -> Prop {
    theorem_prop("concat_map_cons")
}

pub fn concat_map_computes_to_list_source_theorem() -> Prop {
    theorem_prop("concat_map_computes_to_list")
}

pub fn fold_right_nil_source_theorem() -> Prop {
    theorem_prop("fold_right_nil")
}

pub fn fold_right_cons_source_theorem() -> Prop {
    theorem_prop("fold_right_cons")
}

pub fn fold_right_computes_to_value_source_theorem() -> Prop {
    theorem_prop("fold_right_computes_to_value")
}

pub fn fold_left_nil_source_theorem() -> Prop {
    theorem_prop("fold_left_nil")
}

pub fn fold_left_cons_source_theorem() -> Prop {
    theorem_prop("fold_left_cons")
}

pub fn fold_left_computes_to_value_source_theorem() -> Prop {
    theorem_prop("fold_left_computes_to_value")
}

pub fn map_identity_source_theorem() -> Prop {
    theorem_prop("map_identity")
}

pub fn concat_map_singleton_source_theorem() -> Prop {
    theorem_prop("concat_map_singleton")
}

pub fn fold_right_cons_nil_source_theorem() -> Prop {
    theorem_prop("fold_right_cons_nil")
}

pub fn fold_left_reverse_acc_source_theorem() -> Prop {
    theorem_prop("fold_left_reverse_acc")
}

pub fn fold_left_reverse_source_theorem() -> Prop {
    theorem_prop("fold_left_reverse")
}

fn theorem_prop(spelling: &str) -> Prop {
    theorem_definition(spelling).prop
}

fn theorem_definition(spelling: &str) -> ParsedTheorem {
    let module =
        super::parsed_list_module().expect("prelude list source should parse theorem statements");
    let env = super::parsed_prelude_env().expect("prelude source should parse");
    let name = env
        .theorem(spelling)
        .expect("prelude list source should define requested theorem name");

    module
        .theorem(name)
        .cloned()
        .expect("prelude list source should define requested theorem")
}

#[cfg(test)]
fn theorem_symbol(theorem: &str, spelling: &str) -> Symbol {
    theorem_definition(theorem)
        .symbol(spelling)
        .expect("prelude list source should define requested theorem symbol once")
}

#[cfg(test)]
pub(super) fn reverse_computes_to_list_source_result_symbol() -> Symbol {
    theorem_symbol("reverse_computes_to_list", "result")
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

pub fn map_call(function: Computation, list: Computation) -> Computation {
    apply(apply(map(), function), list)
}

pub fn concat_map_call(function: Computation, list: Computation) -> Computation {
    apply(apply(concat_map(), function), list)
}

pub fn fold_right_call(
    function: Computation,
    initial: Computation,
    list: Computation,
) -> Computation {
    apply(apply(apply(fold_right(), function), initial), list)
}

pub fn fold_left_call(
    function: Computation,
    initial: Computation,
    list: Computation,
) -> Computation {
    apply(apply(apply(fold_left(), function), initial), list)
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

/// Mapping over `nil` returns `nil`.
pub fn map_nil_theorem(function: Symbol) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        computes_to(map_call(var(function), nil()), nil()),
    )
}

/// Mapping over a cons applies the function to the head and recurs on the tail.
pub fn map_cons_theorem(function: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                computes_to(
                    map_call(var(function), cons(var(head), var(tail))),
                    cons(
                        apply(var(function), var(head)),
                        map_call(var(function), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// If a function maps every value to a value, mapping it over a list returns a list.
pub fn map_computes_to_list_theorem(
    function: Symbol,
    value: Symbol,
    mapped_value: Symbol,
    list: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        implies(
            forall_where(
                value,
                is_value(var(value)),
                exists_where(
                    mapped_value,
                    is_value(var(mapped_value)),
                    computes_to(apply(var(function), var(value)), var(mapped_value)),
                ),
            ),
            forall_where(
                list,
                is_list(var(list)),
                computes_to_list(result, map_call(var(function), var(list))),
            ),
        ),
    )
}

/// Flat-mapping over `nil` returns `nil`.
pub fn concat_map_nil_theorem(function: Symbol) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        computes_to(concat_map_call(var(function), nil()), nil()),
    )
}

/// Flat-mapping over a cons appends the mapped head to the recursive tail.
pub fn concat_map_cons_theorem(function: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                computes_to(
                    concat_map_call(var(function), cons(var(head), var(tail))),
                    append_call(
                        apply(var(function), var(head)),
                        concat_map_call(var(function), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// If a function maps every value to a list, flat-mapping it returns a list.
pub fn concat_map_computes_to_list_theorem(
    function: Symbol,
    value: Symbol,
    mapped_list: Symbol,
    list: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        implies(
            forall_where(
                value,
                is_value(var(value)),
                computes_to_list(mapped_list, apply(var(function), var(value))),
            ),
            forall_where(
                list,
                is_list(var(list)),
                computes_to_list(result, concat_map_call(var(function), var(list))),
            ),
        ),
    )
}

/// Folding right over `nil` returns the initial value.
pub fn fold_right_nil_theorem(function: Symbol, initial: Symbol) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            initial,
            is_value(var(initial)),
            computes_to(
                fold_right_call(var(function), var(initial), nil()),
                var(initial),
            ),
        ),
    )
}

/// Folding right over a cons combines the head with the folded tail.
pub fn fold_right_cons_theorem(
    function: Symbol,
    initial: Symbol,
    head: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            initial,
            is_value(var(initial)),
            forall_where(
                head,
                is_value(var(head)),
                forall_where(
                    tail,
                    is_list(var(tail)),
                    computes_to(
                        fold_right_call(var(function), var(initial), cons(var(head), var(tail))),
                        apply(
                            apply(var(function), var(head)),
                            fold_right_call(var(function), var(initial), var(tail)),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// If the combining function maps a value and accumulator value to a value,
/// `fold-right` returns a value.
pub fn fold_right_computes_to_value_theorem(
    function: Symbol,
    initial: Symbol,
    value: Symbol,
    accumulator: Symbol,
    folded_value: Symbol,
    list: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            initial,
            is_value(var(initial)),
            implies(
                forall_where(
                    value,
                    is_value(var(value)),
                    forall_where(
                        accumulator,
                        is_value(var(accumulator)),
                        exists_where(
                            folded_value,
                            is_value(var(folded_value)),
                            computes_to(
                                apply(apply(var(function), var(value)), var(accumulator)),
                                var(folded_value),
                            ),
                        ),
                    ),
                ),
                forall_where(
                    list,
                    is_list(var(list)),
                    exists_where(
                        result,
                        is_value(var(result)),
                        computes_to(
                            fold_right_call(var(function), var(initial), var(list)),
                            var(result),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Folding left over `nil` returns the initial value.
pub fn fold_left_nil_theorem(function: Symbol, initial: Symbol) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            initial,
            is_value(var(initial)),
            computes_to(
                fold_left_call(var(function), var(initial), nil()),
                var(initial),
            ),
        ),
    )
}

/// Folding left over a cons combines the current accumulator with the head and
/// recurs on the tail.
pub fn fold_left_cons_theorem(
    function: Symbol,
    initial: Symbol,
    head: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            initial,
            is_value(var(initial)),
            forall_where(
                head,
                is_value(var(head)),
                forall_where(
                    tail,
                    is_list(var(tail)),
                    computes_to(
                        fold_left_call(var(function), var(initial), cons(var(head), var(tail))),
                        fold_left_call(
                            var(function),
                            apply(apply(var(function), var(initial)), var(head)),
                            var(tail),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// If the combining function maps an accumulator value and element value to a
/// value, `fold-left` returns a value.
pub fn fold_left_computes_to_value_theorem(
    function: Symbol,
    accumulator: Symbol,
    value: Symbol,
    folded_value: Symbol,
    list: Symbol,
    initial: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        implies(
            forall_where(
                accumulator,
                is_value(var(accumulator)),
                forall_where(
                    value,
                    is_value(var(value)),
                    exists_where(
                        folded_value,
                        is_value(var(folded_value)),
                        computes_to(
                            apply(apply(var(function), var(accumulator)), var(value)),
                            var(folded_value),
                        ),
                    ),
                ),
            ),
            forall_where(
                list,
                is_list(var(list)),
                forall_where(
                    initial,
                    is_value(var(initial)),
                    exists_where(
                        result,
                        is_value(var(result)),
                        computes_to(
                            fold_left_call(var(function), var(initial), var(list)),
                            var(result),
                        ),
                    ),
                ),
            ),
        ),
    )
}

pub fn identity_function(value: Symbol) -> Computation {
    lambda(value, var(value))
}

pub fn singleton_function(value: Symbol) -> Computation {
    lambda(value, singleton(var(value)))
}

pub fn fold_right_cons_function(value: Symbol, accumulator: Symbol) -> Computation {
    lambda(
        value,
        lambda(accumulator, cons(var(value), var(accumulator))),
    )
}

pub fn fold_left_reverse_function(accumulator: Symbol, value: Symbol) -> Computation {
    lambda(
        accumulator,
        lambda(value, cons(var(value), var(accumulator))),
    )
}

/// Mapping identity over a list returns the list.
pub fn map_identity_theorem(list: Symbol, value: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to(map_call(identity_function(value), var(list)), var(list)),
    )
}

/// Flat-mapping singleton over a list returns the list.
pub fn concat_map_singleton_theorem(list: Symbol, value: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to(
            concat_map_call(singleton_function(value), var(list)),
            var(list),
        ),
    )
}

/// Folding right with `cons` and `nil` rebuilds the input list.
pub fn fold_right_cons_nil_theorem(list: Symbol, value: Symbol, accumulator: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to(
            fold_right_call(
                fold_right_cons_function(value, accumulator),
                nil(),
                var(list),
            ),
            var(list),
        ),
    )
}

/// Folding left with a front-consing function is `reverse_acc`.
pub fn fold_left_reverse_acc_theorem(
    list: Symbol,
    acc: Symbol,
    accumulator: Symbol,
    value: Symbol,
) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        forall_where(
            acc,
            is_list(var(acc)),
            computes_to(
                fold_left_call(
                    fold_left_reverse_function(accumulator, value),
                    var(acc),
                    var(list),
                ),
                reverse_acc_call(var(list), var(acc)),
            ),
        ),
    )
}

/// Folding left with a front-consing function and `nil` reverses the input list.
pub fn fold_left_reverse_theorem(list: Symbol, accumulator: Symbol, value: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to(
            fold_left_call(
                fold_left_reverse_function(accumulator, value),
                nil(),
                var(list),
            ),
            reverse_call(var(list)),
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
    use crate::{
        Effect, Proof, RUNTIME_ERROR, Value, alpha_eq_prop, computes_to, diverges, exists_where,
    };

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
    const FUNCTION: Symbol = Symbol(207);
    const VALUE: Symbol = Symbol(208);
    const MAPPED_VALUE: Symbol = Symbol(209);
    const MAPPED_LIST: Symbol = Symbol(210);
    const INITIAL: Symbol = Symbol(211);
    const FOLDED_VALUE: Symbol = Symbol(212);

    fn prove_evaluation(computation: Computation, expected: impl Into<Outcome>) -> Proof {
        proof_by_evaluation(computation, expected, 512).expect("example should evaluate")
    }

    fn assert_evaluates(computation: Computation, expected: impl Into<Outcome>) {
        let expected = expected.into();
        let proof = prove_evaluation(computation.clone(), expected.clone());
        assert!(check_evaluates_to(computation, expected, &proof));
    }

    fn assert_alpha_eq(left: &Prop, right: &Prop) {
        assert!(
            alpha_eq_prop(left, right),
            "expected alpha-equivalent propositions\nleft: {left:?}\nright: {right:?}"
        );
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
        let list = theorem_symbol("reverse_acc_computes_to_list", "list");
        let acc = theorem_symbol("reverse_acc_computes_to_list", "acc");
        let result = theorem_symbol("reverse_acc_computes_to_list", "result");

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
        let list = theorem_symbol("reverse_computes_to_list", "list");
        let result = theorem_symbol("reverse_computes_to_list", "result");

        assert_eq!(
            reverse_computes_to_list_source_theorem(),
            reverse_computes_to_list_theorem(list, result)
        );
    }

    #[test]
    fn reverse_nil_source_theorem_has_expected_shape() {
        let result = theorem_symbol("reverse_nil_computes_to_list", "result");

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
        let head = theorem_symbol("reverse_singleton", "head");

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
        let list = theorem_symbol("reverse_acc_append", "list");
        let acc = theorem_symbol("reverse_acc_append", "acc");

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
        let head = theorem_symbol("reverse_cons", "head");
        let tail = theorem_symbol("reverse_cons", "tail");

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
        let list = theorem_symbol("reverse_acc_reverse", "list");
        let acc = theorem_symbol("reverse_acc_reverse", "acc");

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
        let list = theorem_symbol("reverse_double", "list");

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
        let left = theorem_symbol("reverse_acc_of_append", "left");
        let right = theorem_symbol("reverse_acc_of_append", "right");
        let acc = theorem_symbol("reverse_acc_of_append", "acc");

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
        let left = theorem_symbol("reverse_append", "left");
        let right = theorem_symbol("reverse_append", "right");

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
        let list = theorem_symbol("snoc_computes_to_list", "list");
        let value = theorem_symbol("snoc_computes_to_list", "value");
        let result = theorem_symbol("snoc_computes_to_list", "result");

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
        let nil_value = theorem_symbol("snoc_nil", "value");
        let cons_head = theorem_symbol("snoc_cons", "head");
        let cons_tail = theorem_symbol("snoc_cons", "tail");
        let cons_value = theorem_symbol("snoc_cons", "value");

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
    fn map_theorems_have_expected_shape() {
        assert_eq!(
            map_nil_theorem(FUNCTION),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                computes_to(map_call(var(FUNCTION), nil()), nil()),
            )
        );
        assert_eq!(
            map_cons_theorem(FUNCTION, HEAD, TAIL),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            map_call(var(FUNCTION), cons(var(HEAD), var(TAIL))),
                            cons(
                                apply(var(FUNCTION), var(HEAD)),
                                map_call(var(FUNCTION), var(TAIL)),
                            ),
                        ),
                    ),
                ),
            )
        );
        assert_eq!(
            map_computes_to_list_theorem(FUNCTION, VALUE, MAPPED_VALUE, X, RESULT),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                implies(
                    forall_where(
                        VALUE,
                        is_value(var(VALUE)),
                        exists_where(
                            MAPPED_VALUE,
                            is_value(var(MAPPED_VALUE)),
                            computes_to(apply(var(FUNCTION), var(VALUE)), var(MAPPED_VALUE),),
                        ),
                    ),
                    forall_where(
                        X,
                        is_list(var(X)),
                        computes_to_list(RESULT, map_call(var(FUNCTION), var(X))),
                    ),
                ),
            )
        );
    }

    #[test]
    fn map_source_theorems_have_expected_shape() {
        let nil_function = theorem_symbol("map_nil", "function");
        let cons_function = theorem_symbol("map_cons", "function");
        let cons_head = theorem_symbol("map_cons", "head");
        let cons_tail = theorem_symbol("map_cons", "tail");
        let computes_function = theorem_symbol("map_computes_to_list", "function");
        let computes_value = theorem_symbol("map_computes_to_list", "value");
        let computes_mapped_value = theorem_symbol("map_computes_to_list", "mapped_value");
        let computes_list = theorem_symbol("map_computes_to_list", "list");
        let computes_result = theorem_symbol("map_computes_to_list", "result");

        assert_eq!(map_nil_source_theorem(), map_nil_theorem(nil_function));
        assert_eq!(
            map_cons_source_theorem(),
            map_cons_theorem(cons_function, cons_head, cons_tail)
        );
        assert_eq!(
            map_computes_to_list_source_theorem(),
            map_computes_to_list_theorem(
                computes_function,
                computes_value,
                computes_mapped_value,
                computes_list,
                computes_result,
            )
        );
    }

    #[test]
    fn concat_map_theorems_have_expected_shape() {
        assert_eq!(
            concat_map_nil_theorem(FUNCTION),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                computes_to(concat_map_call(var(FUNCTION), nil()), nil()),
            )
        );
        assert_eq!(
            concat_map_cons_theorem(FUNCTION, HEAD, TAIL),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            concat_map_call(var(FUNCTION), cons(var(HEAD), var(TAIL))),
                            append_call(
                                apply(var(FUNCTION), var(HEAD)),
                                concat_map_call(var(FUNCTION), var(TAIL)),
                            ),
                        ),
                    ),
                ),
            )
        );
        assert_eq!(
            concat_map_computes_to_list_theorem(FUNCTION, VALUE, MAPPED_LIST, X, RESULT),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                implies(
                    forall_where(
                        VALUE,
                        is_value(var(VALUE)),
                        computes_to_list(MAPPED_LIST, apply(var(FUNCTION), var(VALUE))),
                    ),
                    forall_where(
                        X,
                        is_list(var(X)),
                        computes_to_list(RESULT, concat_map_call(var(FUNCTION), var(X))),
                    ),
                ),
            )
        );
    }

    #[test]
    fn concat_map_source_theorems_have_expected_shape() {
        let nil_function = theorem_symbol("concat_map_nil", "function");
        let cons_function = theorem_symbol("concat_map_cons", "function");
        let cons_head = theorem_symbol("concat_map_cons", "head");
        let cons_tail = theorem_symbol("concat_map_cons", "tail");
        let computes_function = theorem_symbol("concat_map_computes_to_list", "function");
        let computes_value = theorem_symbol("concat_map_computes_to_list", "value");
        let computes_mapped_list = theorem_symbol("concat_map_computes_to_list", "mapped_list");
        let computes_list = theorem_symbol("concat_map_computes_to_list", "list");
        let computes_result = theorem_symbol("concat_map_computes_to_list", "result");

        assert_eq!(
            concat_map_nil_source_theorem(),
            concat_map_nil_theorem(nil_function)
        );
        assert_eq!(
            concat_map_cons_source_theorem(),
            concat_map_cons_theorem(cons_function, cons_head, cons_tail)
        );
        assert_eq!(
            concat_map_computes_to_list_source_theorem(),
            concat_map_computes_to_list_theorem(
                computes_function,
                computes_value,
                computes_mapped_list,
                computes_list,
                computes_result,
            )
        );
    }

    #[test]
    fn fold_right_theorems_have_expected_shape() {
        assert_eq!(
            fold_right_nil_theorem(FUNCTION, INITIAL),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                forall_where(
                    INITIAL,
                    is_value(var(INITIAL)),
                    computes_to(
                        fold_right_call(var(FUNCTION), var(INITIAL), nil()),
                        var(INITIAL),
                    ),
                ),
            )
        );
        assert_eq!(
            fold_right_cons_theorem(FUNCTION, INITIAL, HEAD, TAIL),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                forall_where(
                    INITIAL,
                    is_value(var(INITIAL)),
                    forall_where(
                        HEAD,
                        is_value(var(HEAD)),
                        forall_where(
                            TAIL,
                            is_list(var(TAIL)),
                            computes_to(
                                fold_right_call(
                                    var(FUNCTION),
                                    var(INITIAL),
                                    cons(var(HEAD), var(TAIL)),
                                ),
                                apply(
                                    apply(var(FUNCTION), var(HEAD)),
                                    fold_right_call(var(FUNCTION), var(INITIAL), var(TAIL)),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        );
        assert_eq!(
            fold_right_computes_to_value_theorem(
                FUNCTION,
                INITIAL,
                VALUE,
                ACCUMULATOR,
                FOLDED_VALUE,
                X,
                RESULT,
            ),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                forall_where(
                    INITIAL,
                    is_value(var(INITIAL)),
                    implies(
                        forall_where(
                            VALUE,
                            is_value(var(VALUE)),
                            forall_where(
                                ACCUMULATOR,
                                is_value(var(ACCUMULATOR)),
                                exists_where(
                                    FOLDED_VALUE,
                                    is_value(var(FOLDED_VALUE)),
                                    computes_to(
                                        apply(apply(var(FUNCTION), var(VALUE)), var(ACCUMULATOR),),
                                        var(FOLDED_VALUE),
                                    ),
                                ),
                            ),
                        ),
                        forall_where(
                            X,
                            is_list(var(X)),
                            exists_where(
                                RESULT,
                                is_value(var(RESULT)),
                                computes_to(
                                    fold_right_call(var(FUNCTION), var(INITIAL), var(X)),
                                    var(RESULT),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn fold_right_source_theorems_have_expected_shape() {
        let nil_function = theorem_symbol("fold_right_nil", "function");
        let nil_initial = theorem_symbol("fold_right_nil", "initial");
        let cons_function = theorem_symbol("fold_right_cons", "function");
        let cons_initial = theorem_symbol("fold_right_cons", "initial");
        let cons_head = theorem_symbol("fold_right_cons", "head");
        let cons_tail = theorem_symbol("fold_right_cons", "tail");
        let computes_function = theorem_symbol("fold_right_computes_to_value", "function");
        let computes_initial = theorem_symbol("fold_right_computes_to_value", "initial");
        let computes_value = theorem_symbol("fold_right_computes_to_value", "value");
        let computes_accumulator = theorem_symbol("fold_right_computes_to_value", "accumulator");
        let computes_folded_value = theorem_symbol("fold_right_computes_to_value", "folded_value");
        let computes_list = theorem_symbol("fold_right_computes_to_value", "list");
        let computes_result = theorem_symbol("fold_right_computes_to_value", "result");

        assert_eq!(
            fold_right_nil_source_theorem(),
            fold_right_nil_theorem(nil_function, nil_initial)
        );
        assert_eq!(
            fold_right_cons_source_theorem(),
            fold_right_cons_theorem(cons_function, cons_initial, cons_head, cons_tail)
        );
        assert_eq!(
            fold_right_computes_to_value_source_theorem(),
            fold_right_computes_to_value_theorem(
                computes_function,
                computes_initial,
                computes_value,
                computes_accumulator,
                computes_folded_value,
                computes_list,
                computes_result,
            )
        );
    }

    #[test]
    fn fold_left_theorems_have_expected_shape() {
        assert_eq!(
            fold_left_nil_theorem(FUNCTION, INITIAL),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                forall_where(
                    INITIAL,
                    is_value(var(INITIAL)),
                    computes_to(
                        fold_left_call(var(FUNCTION), var(INITIAL), nil()),
                        var(INITIAL),
                    ),
                ),
            )
        );
        assert_eq!(
            fold_left_cons_theorem(FUNCTION, INITIAL, HEAD, TAIL),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                forall_where(
                    INITIAL,
                    is_value(var(INITIAL)),
                    forall_where(
                        HEAD,
                        is_value(var(HEAD)),
                        forall_where(
                            TAIL,
                            is_list(var(TAIL)),
                            computes_to(
                                fold_left_call(
                                    var(FUNCTION),
                                    var(INITIAL),
                                    cons(var(HEAD), var(TAIL)),
                                ),
                                fold_left_call(
                                    var(FUNCTION),
                                    apply(apply(var(FUNCTION), var(INITIAL)), var(HEAD)),
                                    var(TAIL),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        );
        assert_eq!(
            fold_left_computes_to_value_theorem(
                FUNCTION,
                ACCUMULATOR,
                VALUE,
                FOLDED_VALUE,
                X,
                INITIAL,
                RESULT,
            ),
            forall_where(
                FUNCTION,
                is_value(var(FUNCTION)),
                implies(
                    forall_where(
                        ACCUMULATOR,
                        is_value(var(ACCUMULATOR)),
                        forall_where(
                            VALUE,
                            is_value(var(VALUE)),
                            exists_where(
                                FOLDED_VALUE,
                                is_value(var(FOLDED_VALUE)),
                                computes_to(
                                    apply(apply(var(FUNCTION), var(ACCUMULATOR)), var(VALUE),),
                                    var(FOLDED_VALUE),
                                ),
                            ),
                        ),
                    ),
                    forall_where(
                        X,
                        is_list(var(X)),
                        forall_where(
                            INITIAL,
                            is_value(var(INITIAL)),
                            exists_where(
                                RESULT,
                                is_value(var(RESULT)),
                                computes_to(
                                    fold_left_call(var(FUNCTION), var(INITIAL), var(X)),
                                    var(RESULT),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn fold_left_source_theorems_have_expected_shape() {
        let nil_function = theorem_symbol("fold_left_nil", "function");
        let nil_initial = theorem_symbol("fold_left_nil", "initial");
        let cons_function = theorem_symbol("fold_left_cons", "function");
        let cons_initial = theorem_symbol("fold_left_cons", "initial");
        let cons_head = theorem_symbol("fold_left_cons", "head");
        let cons_tail = theorem_symbol("fold_left_cons", "tail");
        let computes_function = theorem_symbol("fold_left_computes_to_value", "function");
        let computes_accumulator = theorem_symbol("fold_left_computes_to_value", "accumulator");
        let computes_value = theorem_symbol("fold_left_computes_to_value", "value");
        let computes_folded_value = theorem_symbol("fold_left_computes_to_value", "folded_value");
        let computes_list = theorem_symbol("fold_left_computes_to_value", "list");
        let computes_initial = theorem_symbol("fold_left_computes_to_value", "initial");
        let computes_result = theorem_symbol("fold_left_computes_to_value", "result");

        assert_eq!(
            fold_left_nil_source_theorem(),
            fold_left_nil_theorem(nil_function, nil_initial)
        );
        assert_eq!(
            fold_left_cons_source_theorem(),
            fold_left_cons_theorem(cons_function, cons_initial, cons_head, cons_tail)
        );
        assert_eq!(
            fold_left_computes_to_value_source_theorem(),
            fold_left_computes_to_value_theorem(
                computes_function,
                computes_accumulator,
                computes_value,
                computes_folded_value,
                computes_list,
                computes_initial,
                computes_result,
            )
        );
    }

    #[test]
    fn higher_order_relation_source_theorems_have_expected_shape() {
        assert_alpha_eq(
            &map_identity_source_theorem(),
            &map_identity_theorem(X, VALUE),
        );
        assert_alpha_eq(
            &concat_map_singleton_source_theorem(),
            &concat_map_singleton_theorem(X, VALUE),
        );
        assert_alpha_eq(
            &fold_right_cons_nil_source_theorem(),
            &fold_right_cons_nil_theorem(X, VALUE, ACCUMULATOR),
        );
        assert_alpha_eq(
            &fold_left_reverse_acc_source_theorem(),
            &fold_left_reverse_acc_theorem(X, ACCUMULATOR, INITIAL, VALUE),
        );
        assert_alpha_eq(
            &fold_left_reverse_source_theorem(),
            &fold_left_reverse_theorem(X, ACCUMULATOR, VALUE),
        );
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
        let singleton_head = theorem_symbol("last_singleton", "head");
        let cons_head = theorem_symbol("last_cons", "head");
        let cons_next = theorem_symbol("last_cons", "next");
        let cons_tail = theorem_symbol("last_cons", "tail");

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
        let singleton_head = theorem_symbol("init_singleton", "head");
        let cons_head = theorem_symbol("init_cons", "head");
        let cons_next = theorem_symbol("init_cons", "next");
        let cons_tail = theorem_symbol("init_cons", "tail");

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
        let cons_head = theorem_symbol("null_cons", "head");
        let cons_tail = theorem_symbol("null_cons", "tail");

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
        let singleton_head = theorem_symbol("is_singleton_singleton", "head");
        let cons_head = theorem_symbol("is_singleton_cons", "head");
        let cons_next = theorem_symbol("is_singleton_cons", "next");
        let cons_tail = theorem_symbol("is_singleton_cons", "tail");

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
        let right = theorem_symbol("append_nil_computes_to_list", "right");
        let result = theorem_symbol("append_nil_computes_to_list", "result");

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
        let left = theorem_symbol("append_computes_to_list", "left");
        let right = theorem_symbol("append_computes_to_list", "right");
        let result = theorem_symbol("append_computes_to_list", "result");

        assert_eq!(
            append_computes_to_list_source_theorem(),
            append_computes_to_list_theorem(left, right, result)
        );
    }

    #[test]
    fn append_nil_returns_right_source_theorem_has_expected_shape() {
        let right = theorem_symbol("append_nil_returns_right", "right");

        assert_eq!(
            append_nil_returns_right_source_theorem(),
            append_nil_returns_right_theorem(right)
        );
    }

    #[test]
    fn append_right_nil_source_theorem_has_expected_shape() {
        let left = theorem_symbol("append_right_nil", "left");

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
        let head = theorem_symbol("append_cons", "head");
        let tail = theorem_symbol("append_cons", "tail");
        let right = theorem_symbol("append_cons", "right");

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
        let head = theorem_symbol("append_singleton", "head");
        let right = theorem_symbol("append_singleton", "right");

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
        let left = theorem_symbol("append_assoc", "left");
        let middle = theorem_symbol("append_assoc", "middle");
        let right = theorem_symbol("append_assoc", "right");

        assert_eq!(
            append_assoc_source_theorem(),
            append_assoc_theorem(left, middle, right)
        );
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
    fn map_nil_returns_nil() {
        let identity = lambda(X, var(X));

        assert_evaluates(map_call(identity, nil()), Value::nil());
    }

    #[test]
    fn map_identity_returns_same_list() {
        let identity = lambda(X, var(X));

        assert_evaluates(
            map_call(identity, triple(quote(A), quote(B), quote(NOT_A_LIST))),
            value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
        );
    }

    #[test]
    fn map_constant_returns_constant_list() {
        let constant_unit = lambda(X, unit());

        assert_evaluates(
            map_call(constant_unit, pair(quote(A), quote(B))),
            value(pair(unit(), unit())),
        );
    }

    #[test]
    fn concat_map_nil_returns_nil() {
        let singleton_function = lambda(X, singleton(var(X)));

        assert_evaluates(concat_map_call(singleton_function, nil()), Value::nil());
    }

    #[test]
    fn concat_map_singleton_function_flattens() {
        let singleton_function = lambda(X, singleton(var(X)));

        assert_evaluates(
            concat_map_call(singleton_function, pair(quote(A), quote(B))),
            value(pair(quote(A), quote(B))),
        );
    }

    #[test]
    fn concat_map_pair_function_flattens() {
        let pair_function = lambda(X, pair(var(X), var(X)));
        let expected = cons(quote(A), cons(quote(A), pair(quote(B), quote(B))));

        assert_evaluates(
            concat_map_call(pair_function, pair(quote(A), quote(B))),
            value(expected),
        );
    }

    #[test]
    fn fold_right_nil_returns_initial() {
        let cons_function = lambda(X, lambda(ACCUMULATOR, cons(var(X), var(ACCUMULATOR))));

        assert_evaluates(fold_right_call(cons_function, nil(), nil()), Value::nil());
    }

    #[test]
    fn fold_right_cons_function_rebuilds_list() {
        let cons_function = lambda(X, lambda(ACCUMULATOR, cons(var(X), var(ACCUMULATOR))));

        assert_evaluates(
            fold_right_call(cons_function, nil(), triple(quote(A), quote(B), unit())),
            value(triple(quote(A), quote(B), unit())),
        );
    }

    #[test]
    fn fold_right_accumulator_function_returns_initial() {
        let accumulator_function = lambda(X, lambda(ACCUMULATOR, var(ACCUMULATOR)));

        assert_evaluates(
            fold_right_call(accumulator_function, unit(), pair(quote(A), quote(B))),
            Value::quote(prelude_symbol("unit")),
        );
    }

    #[test]
    fn fold_left_nil_returns_initial() {
        let accumulator_function = lambda(ACCUMULATOR, lambda(X, var(ACCUMULATOR)));

        assert_evaluates(
            fold_left_call(accumulator_function, unit(), nil()),
            Value::quote(prelude_symbol("unit")),
        );
    }

    #[test]
    fn fold_left_front_cons_reverses_list() {
        let front_cons = fold_left_reverse_function(ACCUMULATOR, X);

        assert_evaluates(
            fold_left_call(front_cons, nil(), triple(quote(A), quote(B), unit())),
            value(triple(unit(), quote(B), quote(A))),
        );
    }

    #[test]
    fn fold_left_front_cons_with_accumulates_prefix() {
        let front_cons = fold_left_reverse_function(ACCUMULATOR, X);

        assert_evaluates(
            fold_left_call(front_cons, singleton(unit()), pair(quote(A), quote(B))),
            value(triple(quote(B), quote(A), unit())),
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
        assert_evaluates(null_call(nil()), Value::quote(prelude_symbol(":true")));
    }

    #[test]
    fn null_cons_returns_false() {
        assert_evaluates(
            null_call(singleton(quote(A))),
            Value::quote(prelude_symbol(":false")),
        );
    }

    #[test]
    fn is_singleton_nil_returns_false() {
        assert_evaluates(
            is_singleton_call(nil()),
            Value::quote(prelude_symbol(":false")),
        );
    }

    #[test]
    fn is_singleton_singleton_returns_true() {
        assert_evaluates(
            is_singleton_call(singleton(quote(A))),
            Value::quote(prelude_symbol(":true")),
        );
    }

    #[test]
    fn is_singleton_pair_returns_false() {
        assert_evaluates(
            is_singleton_call(pair(quote(A), quote(B))),
            Value::quote(prelude_symbol(":false")),
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
