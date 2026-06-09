//! Test helpers and expected shapes for the list prelude source.

use crate::{
    Computation, LAMBDA_KIND_SYMBOL, LIST_KIND_SYMBOL, Lambda, Outcome, Proof, Prop, RUNTIME_ERROR,
    SYMBOL_KIND_SYMBOL, Symbol, Theory, and, computes_to, computes_to_list,
    elab::{proof, source::ParsedTheorem},
    equal, errors_with, exists_where, forall, forall_where, implies, is_bool, is_list, is_value,
    symbol_eq, value_kind,
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

pub fn length() -> Computation {
    computation_ref("length")
}

pub fn length_definition() -> Computation {
    definition("length")
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

pub fn zip_with() -> Computation {
    computation_ref("zip-with")
}

pub fn zip_with_definition() -> Computation {
    definition("zip-with")
}

pub fn filter() -> Computation {
    computation_ref("filter")
}

pub fn filter_definition() -> Computation {
    definition("filter")
}

pub fn any() -> Computation {
    computation_ref("any")
}

pub fn any_definition() -> Computation {
    definition("any")
}

pub fn all() -> Computation {
    computation_ref("all")
}

pub fn all_definition() -> Computation {
    definition("all")
}

pub fn is_symbol_definition() -> Computation {
    definition("is-symbol")
}

pub fn is_lambda_definition() -> Computation {
    definition("is-lambda")
}

pub fn is_list_value_definition() -> Computation {
    definition("is-list-value")
}

pub fn value_eq() -> Computation {
    computation_ref("value-eq")
}

pub fn value_eq_definition() -> Computation {
    definition("value-eq")
}

pub fn value_eq_comparable() -> Computation {
    computation_ref("value-eq-comparable")
}

pub fn value_eq_comparable_definition() -> Computation {
    definition("value-eq-comparable")
}

pub fn member() -> Computation {
    computation_ref("member")
}

pub fn member_definition() -> Computation {
    definition("member")
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
    let modules = super::parsed_list_modules().expect("prelude list source should parse");
    let env = super::parsed_prelude_env().expect("prelude source should parse");
    let name = env
        .computation(spelling)
        .expect("prelude list source should define requested computation name");

    modules
        .iter()
        .find_map(|module| module.computation(name))
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

pub fn length_nil_source_theorem() -> Prop {
    theorem_prop("length_nil")
}

pub fn length_cons_source_theorem() -> Prop {
    theorem_prop("length_cons")
}

pub fn length_singleton_source_theorem() -> Prop {
    theorem_prop("length_singleton")
}

pub fn length_computes_to_list_source_theorem() -> Prop {
    theorem_prop("length_computes_to_list")
}

pub fn length_append_source_theorem() -> Prop {
    theorem_prop("length_append")
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

pub fn length_map_source_theorem() -> Prop {
    theorem_prop("length_map")
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

pub fn zip_with_left_nil_source_theorem() -> Prop {
    theorem_prop("zip_with_left_nil")
}

pub fn zip_with_right_nil_source_theorem() -> Prop {
    theorem_prop("zip_with_right_nil")
}

pub fn zip_with_cons_source_theorem() -> Prop {
    theorem_prop("zip_with_cons")
}

pub fn zip_with_computes_to_list_source_theorem() -> Prop {
    theorem_prop("zip_with_computes_to_list")
}

pub fn filter_nil_source_theorem() -> Prop {
    theorem_prop("filter_nil")
}

pub fn filter_cons_true_source_theorem() -> Prop {
    theorem_prop("filter_cons_true")
}

pub fn filter_cons_false_source_theorem() -> Prop {
    theorem_prop("filter_cons_false")
}

pub fn filter_computes_to_list_source_theorem() -> Prop {
    theorem_prop("filter_computes_to_list")
}

pub fn any_nil_source_theorem() -> Prop {
    theorem_prop("any_nil")
}

pub fn any_cons_true_source_theorem() -> Prop {
    theorem_prop("any_cons_true")
}

pub fn any_cons_false_source_theorem() -> Prop {
    theorem_prop("any_cons_false")
}

pub fn any_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("any_computes_to_bool")
}

pub fn value_eq_true_true_source_theorem() -> Prop {
    theorem_prop("value_eq_true_true")
}

pub fn value_eq_true_false_source_theorem() -> Prop {
    theorem_prop("value_eq_true_false")
}

pub fn value_eq_nil_source_theorem() -> Prop {
    theorem_prop("value_eq_nil")
}

pub fn value_eq_nil_cons_source_theorem() -> Prop {
    theorem_prop("value_eq_nil_cons")
}

pub fn value_eq_cons_nil_source_theorem() -> Prop {
    theorem_prop("value_eq_cons_nil")
}

pub fn value_eq_cons_source_theorem() -> Prop {
    theorem_prop("value_eq_cons")
}

pub fn value_kind_symbol_implies_is_symbol_source_theorem() -> Prop {
    theorem_prop("value_kind_symbol_implies_is_symbol")
}

pub fn value_kind_lambda_implies_is_lambda_source_theorem() -> Prop {
    theorem_prop("value_kind_lambda_implies_is_lambda")
}

pub fn is_symbol_true_implies_is_lambda_false_source_theorem() -> Prop {
    theorem_prop("is_symbol_true_implies_is_lambda_false")
}

pub fn value_eq_comparable_symbol_source_theorem() -> Prop {
    theorem_prop("value_eq_comparable_symbol")
}

pub fn value_eq_comparable_nil_source_theorem() -> Prop {
    theorem_prop("value_eq_comparable_nil")
}

pub fn value_eq_comparable_cons_source_theorem() -> Prop {
    theorem_prop("value_eq_comparable_cons")
}

pub fn value_eq_true_implies_not_lambdas_source_theorem() -> Prop {
    theorem_prop("value_eq_true_implies_not_lambdas")
}

pub fn value_non_symbol_non_lambda_is_list_source_theorem() -> Prop {
    theorem_prop("value_non_symbol_non_lambda_is_list")
}

pub fn value_eq_left_non_symbol_true_implies_lists_source_theorem() -> Prop {
    theorem_prop("value_eq_left_non_symbol_true_implies_lists")
}

pub fn value_eq_left_symbol_true_source_theorem() -> Prop {
    theorem_prop("value_eq_left_symbol_true")
}

pub fn value_eq_left_symbol_sound_source_theorem() -> Prop {
    theorem_prop("value_eq_left_symbol_sound")
}

pub fn value_eq_cons_true_elim_source_theorem() -> Prop {
    theorem_prop("value_eq_cons_true_elim")
}

pub fn cons_congr_source_theorem() -> Prop {
    theorem_prop("cons_congr")
}

pub fn value_eq_sound_source_theorem() -> Prop {
    theorem_prop("value_eq_sound")
}

pub fn value_eq_refl_source_theorem() -> Prop {
    theorem_prop("value_eq_refl")
}

pub fn value_eq_true_implies_comparable_left_source_theorem() -> Prop {
    theorem_prop("value_eq_true_implies_comparable_left")
}

pub fn value_eq_true_implies_comparable_right_source_theorem() -> Prop {
    theorem_prop("value_eq_true_implies_comparable_right")
}

pub fn value_eq_symm_source_theorem() -> Prop {
    theorem_prop("value_eq_symm")
}

pub fn member_nil_source_theorem() -> Prop {
    theorem_prop("member_nil")
}

pub fn member_cons_true_source_theorem() -> Prop {
    theorem_prop("member_cons_true")
}

pub fn member_cons_false_source_theorem() -> Prop {
    theorem_prop("member_cons_false")
}

pub fn all_nil_source_theorem() -> Prop {
    theorem_prop("all_nil")
}

pub fn all_cons_true_source_theorem() -> Prop {
    theorem_prop("all_cons_true")
}

pub fn all_cons_false_source_theorem() -> Prop {
    theorem_prop("all_cons_false")
}

pub fn all_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("all_computes_to_bool")
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
    let modules =
        super::parsed_list_modules().expect("prelude list source should parse theorem statements");
    let env = super::parsed_prelude_env().expect("prelude source should parse");
    let name = env
        .theorem(spelling)
        .expect("prelude list source should define requested theorem name");

    modules
        .iter()
        .find_map(|module| module.theorem(name))
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

pub fn length_call(list: Computation) -> Computation {
    apply(length(), list)
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

pub fn zip_with_call(function: Computation, left: Computation, right: Computation) -> Computation {
    apply(apply(apply(zip_with(), function), left), right)
}

pub fn filter_call(predicate: Computation, list: Computation) -> Computation {
    apply(apply(filter(), predicate), list)
}

pub fn any_call(predicate: Computation, list: Computation) -> Computation {
    apply(apply(any(), predicate), list)
}

pub fn all_call(predicate: Computation, list: Computation) -> Computation {
    apply(apply(all(), predicate), list)
}

pub fn is_symbol_call(value: Computation) -> Computation {
    symbol_eq(value_kind(value), quote(SYMBOL_KIND_SYMBOL))
}

pub fn is_lambda_call(value: Computation) -> Computation {
    symbol_eq(value_kind(value), quote(LAMBDA_KIND_SYMBOL))
}

pub fn is_list_value_call(value: Computation) -> Computation {
    symbol_eq(value_kind(value), quote(LIST_KIND_SYMBOL))
}

pub fn value_eq_call(left: Computation, right: Computation) -> Computation {
    apply(apply(value_eq(), left), right)
}

pub fn value_eq_comparable_call(value: Computation) -> Computation {
    apply(value_eq_comparable(), value)
}

pub fn head_call(list: Computation) -> Computation {
    Computation::Head(Box::new(list))
}

pub fn tail_call(list: Computation) -> Computation {
    Computation::Tail(Box::new(list))
}

pub fn if_call(
    condition: Computation,
    then_branch: Computation,
    else_branch: Computation,
) -> Computation {
    Computation::If {
        condition: Box::new(condition),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn member_call(value: Computation, list: Computation) -> Computation {
    apply(apply(member(), value), list)
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

/// The length of `nil` is zero, represented as `nil`.
pub fn length_nil_theorem() -> Prop {
    computes_to(length_call(nil()), nil())
}

/// The length of a cons is one plus the length of its tail.
pub fn length_cons_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            computes_to(
                length_call(cons(var(head), var(tail))),
                cons(unit(), length_call(var(tail))),
            ),
        ),
    )
}

/// The length of a singleton is one.
pub fn length_singleton_theorem(head: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        computes_to(length_call(singleton(var(head))), singleton(unit())),
    )
}

/// If `list` is a list, then `length(list)` computes to a list-shaped nat.
pub fn length_computes_to_list_theorem(list: Symbol, result: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to_list(result, length_call(var(list))),
    )
}

/// Length distributes over append, with unary addition represented by append.
pub fn length_append_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        forall_where(
            right,
            is_list(var(right)),
            computes_to(
                length_call(append_call(var(left), var(right))),
                append_call(length_call(var(left)), length_call(var(right))),
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

/// Mapping a value-producing function preserves length.
pub fn length_map_theorem(
    function: Symbol,
    value: Symbol,
    mapped_value: Symbol,
    list: Symbol,
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
                computes_to(
                    length_call(map_call(var(function), var(list))),
                    length_call(var(list)),
                ),
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

/// Zipping with an empty left list returns `nil`.
pub fn zip_with_left_nil_theorem(function: Symbol, right: Symbol) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            right,
            is_list(var(right)),
            computes_to(zip_with_call(var(function), nil(), var(right)), nil()),
        ),
    )
}

/// Zipping with an empty right list returns `nil`.
pub fn zip_with_right_nil_theorem(function: Symbol, left: Symbol) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            left,
            is_list(var(left)),
            computes_to(zip_with_call(var(function), var(left), nil()), nil()),
        ),
    )
}

/// Zipping two conses combines the heads and recurs on the tails.
pub fn zip_with_cons_theorem(
    function: Symbol,
    left_head: Symbol,
    left_tail: Symbol,
    right_head: Symbol,
    right_tail: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            left_head,
            is_value(var(left_head)),
            forall_where(
                left_tail,
                is_list(var(left_tail)),
                forall_where(
                    right_head,
                    is_value(var(right_head)),
                    forall_where(
                        right_tail,
                        is_list(var(right_tail)),
                        computes_to(
                            zip_with_call(
                                var(function),
                                cons(var(left_head), var(left_tail)),
                                cons(var(right_head), var(right_tail)),
                            ),
                            cons(
                                apply(apply(var(function), var(left_head)), var(right_head)),
                                zip_with_call(var(function), var(left_tail), var(right_tail)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// If the combining function maps two values to a value, `zip-with` returns a list.
pub fn zip_with_computes_to_list_theorem(
    function: Symbol,
    left_value: Symbol,
    right_value: Symbol,
    zipped_value: Symbol,
    left: Symbol,
    right: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        implies(
            forall_where(
                left_value,
                is_value(var(left_value)),
                forall_where(
                    right_value,
                    is_value(var(right_value)),
                    exists_where(
                        zipped_value,
                        is_value(var(zipped_value)),
                        computes_to(
                            apply(apply(var(function), var(left_value)), var(right_value)),
                            var(zipped_value),
                        ),
                    ),
                ),
            ),
            forall_where(
                left,
                is_list(var(left)),
                forall_where(
                    right,
                    is_list(var(right)),
                    computes_to_list(result, zip_with_call(var(function), var(left), var(right))),
                ),
            ),
        ),
    )
}

/// Filtering `nil` returns `nil`.
pub fn filter_nil_theorem(predicate: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        computes_to(filter_call(var(predicate), nil()), nil()),
    )
}

/// If the predicate returns true for the head, filtering a cons keeps the head.
pub fn filter_cons_true_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                implies(
                    computes_to(apply(var(predicate), var(head)), true_value()),
                    computes_to(
                        filter_call(var(predicate), cons(var(head), var(tail))),
                        cons(var(head), filter_call(var(predicate), var(tail))),
                    ),
                ),
            ),
        ),
    )
}

/// If the predicate returns false for the head, filtering a cons drops the head.
pub fn filter_cons_false_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                implies(
                    computes_to(apply(var(predicate), var(head)), false_value()),
                    computes_to(
                        filter_call(var(predicate), cons(var(head), var(tail))),
                        filter_call(var(predicate), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// If the predicate returns booleans, filtering returns a list.
pub fn filter_computes_to_list_theorem(
    predicate: Symbol,
    value: Symbol,
    list: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        implies(
            forall_where(
                value,
                is_value(var(value)),
                is_bool(apply(var(predicate), var(value))),
            ),
            forall_where(
                list,
                is_list(var(list)),
                computes_to_list(result, filter_call(var(predicate), var(list))),
            ),
        ),
    )
}

/// `any` over `nil` returns false.
pub fn any_nil_theorem(predicate: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        computes_to(any_call(var(predicate), nil()), false_value()),
    )
}

/// If the predicate returns true for the head, `any` over a cons returns true.
pub fn any_cons_true_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                implies(
                    computes_to(apply(var(predicate), var(head)), true_value()),
                    computes_to(
                        any_call(var(predicate), cons(var(head), var(tail))),
                        true_value(),
                    ),
                ),
            ),
        ),
    )
}

/// If the predicate returns false for the head, `any` recurs on the tail.
pub fn any_cons_false_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                implies(
                    computes_to(apply(var(predicate), var(head)), false_value()),
                    computes_to(
                        any_call(var(predicate), cons(var(head), var(tail))),
                        any_call(var(predicate), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// If the predicate returns booleans, `any` returns a boolean.
pub fn any_computes_to_bool_theorem(predicate: Symbol, value: Symbol, list: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        implies(
            forall_where(
                value,
                is_value(var(value)),
                is_bool(apply(var(predicate), var(value))),
            ),
            forall_where(
                list,
                is_list(var(list)),
                is_bool(any_call(var(predicate), var(list))),
            ),
        ),
    )
}

/// The reserved true symbol equals itself under `value-eq`.
pub fn value_eq_true_true_theorem() -> Prop {
    computes_to(value_eq_call(true_value(), true_value()), true_value())
}

/// Distinct reserved boolean symbols differ under `value-eq`.
pub fn value_eq_true_false_theorem() -> Prop {
    computes_to(value_eq_call(true_value(), false_value()), false_value())
}

/// `nil` equals itself under `value-eq`.
pub fn value_eq_nil_theorem() -> Prop {
    computes_to(value_eq_call(nil(), nil()), true_value())
}

/// `nil` does not equal a cons list under `value-eq`.
pub fn value_eq_nil_cons_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            computes_to(
                value_eq_call(nil(), cons(var(head), var(tail))),
                false_value(),
            ),
        ),
    )
}

/// A cons list does not equal `nil` under `value-eq`.
pub fn value_eq_cons_nil_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            computes_to(
                value_eq_call(cons(var(head), var(tail)), nil()),
                false_value(),
            ),
        ),
    )
}

/// Cons equality reduces to head equality and then tail equality.
pub fn value_eq_cons_theorem(
    left_head: Symbol,
    left_tail: Symbol,
    right_head: Symbol,
    right_tail: Symbol,
) -> Prop {
    forall_where(
        left_head,
        is_value(var(left_head)),
        forall_where(
            left_tail,
            is_list(var(left_tail)),
            forall_where(
                right_head,
                is_value(var(right_head)),
                forall_where(
                    right_tail,
                    is_list(var(right_tail)),
                    computes_to(
                        value_eq_call(
                            cons(var(left_head), var(left_tail)),
                            cons(var(right_head), var(right_tail)),
                        ),
                        if_call(
                            value_eq_call(
                                head_call(cons(var(left_head), var(left_tail))),
                                head_call(cons(var(right_head), var(right_tail))),
                            ),
                            value_eq_call(
                                tail_call(cons(var(left_head), var(left_tail))),
                                tail_call(cons(var(right_head), var(right_tail))),
                            ),
                            false_value(),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// A true symbol-kind test gives a true `is-symbol` result.
pub fn value_kind_symbol_implies_is_symbol_theorem(value: Symbol) -> Prop {
    forall(
        value,
        implies(
            computes_to(
                symbol_eq(value_kind(var(value)), quote(SYMBOL_KIND_SYMBOL)),
                true_value(),
            ),
            computes_to(is_symbol_call(var(value)), true_value()),
        ),
    )
}

/// A true lambda-kind test gives a true `is-lambda` result.
pub fn value_kind_lambda_implies_is_lambda_theorem(value: Symbol) -> Prop {
    forall(
        value,
        implies(
            computes_to(
                symbol_eq(value_kind(var(value)), quote(LAMBDA_KIND_SYMBOL)),
                true_value(),
            ),
            computes_to(is_lambda_call(var(value)), true_value()),
        ),
    )
}

/// A computation whose symbol-kind test returns true has a false lambda-kind test.
pub fn is_symbol_true_implies_is_lambda_false_theorem(value: Symbol) -> Prop {
    forall(
        value,
        implies(
            computes_to(is_symbol_call(var(value)), true_value()),
            computes_to(is_lambda_call(var(value)), false_value()),
        ),
    )
}

/// Symbols are comparable by `value-eq`.
pub fn value_eq_comparable_symbol_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        implies(
            computes_to(is_symbol_call(var(value)), true_value()),
            computes_to(value_eq_comparable_call(var(value)), true_value()),
        ),
    )
}

/// `nil` is comparable by `value-eq`.
pub fn value_eq_comparable_nil_theorem() -> Prop {
    computes_to(value_eq_comparable_call(nil()), true_value())
}

/// A cons is comparable when its head and tail are comparable.
pub fn value_eq_comparable_cons_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            implies(
                computes_to(value_eq_comparable_call(var(head)), true_value()),
                implies(
                    computes_to(value_eq_comparable_call(var(tail)), true_value()),
                    computes_to(
                        value_eq_comparable_call(cons(var(head), var(tail))),
                        true_value(),
                    ),
                ),
            ),
        ),
    )
}

/// If `value-eq` returns true, neither compared value is a lambda.
pub fn value_eq_true_implies_not_lambdas_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            right,
            is_value(var(right)),
            implies(
                computes_to(value_eq_call(var(left), var(right)), true_value()),
                and(
                    computes_to(is_lambda_call(var(left)), false_value()),
                    computes_to(is_lambda_call(var(right)), false_value()),
                ),
            ),
        ),
    )
}

/// Any value whose kind is neither symbol nor lambda is a list.
pub fn value_non_symbol_non_lambda_is_list_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        implies(
            computes_to(is_symbol_call(var(value)), false_value()),
            implies(
                computes_to(is_lambda_call(var(value)), false_value()),
                is_list(var(value)),
            ),
        ),
    )
}

/// If `value-eq` returns true for a non-symbol left value, both values are lists.
pub fn value_eq_left_non_symbol_true_implies_lists_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        implies(
            computes_to(is_symbol_call(var(left)), false_value()),
            forall_where(
                right,
                is_value(var(right)),
                implies(
                    computes_to(value_eq_call(var(left), var(right)), true_value()),
                    and(is_list(var(left)), is_list(var(right))),
                ),
            ),
        ),
    )
}

/// If `value-eq` succeeds with a known left symbol, the values compute equally.
pub fn value_eq_left_symbol_true_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        implies(
            computes_to(is_symbol_call(var(left)), true_value()),
            forall_where(
                right,
                is_value(var(right)),
                implies(
                    computes_to(is_lambda_call(var(right)), false_value()),
                    implies(
                        computes_to(value_eq_call(var(left), var(right)), true_value()),
                        computes_to(var(left), var(right)),
                    ),
                ),
            ),
        ),
    )
}

/// If `value-eq` succeeds with a known left symbol, the values compute equally.
pub fn value_eq_left_symbol_sound_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        implies(
            computes_to(is_symbol_call(var(left)), true_value()),
            forall_where(
                right,
                is_value(var(right)),
                implies(
                    computes_to(value_eq_call(var(left), var(right)), true_value()),
                    computes_to(var(left), var(right)),
                ),
            ),
        ),
    )
}

/// If cons `value-eq` returns true, both heads and tails return true under `value-eq`.
pub fn value_eq_cons_true_elim_theorem(
    left_head: Symbol,
    left_tail: Symbol,
    right_head: Symbol,
    right_tail: Symbol,
) -> Prop {
    forall_where(
        left_head,
        is_value(var(left_head)),
        forall_where(
            left_tail,
            is_list(var(left_tail)),
            forall_where(
                right_head,
                is_value(var(right_head)),
                forall_where(
                    right_tail,
                    is_list(var(right_tail)),
                    implies(
                        computes_to(
                            value_eq_call(
                                cons(var(left_head), var(left_tail)),
                                cons(var(right_head), var(right_tail)),
                            ),
                            true_value(),
                        ),
                        and(
                            computes_to(
                                value_eq_call(var(left_head), var(right_head)),
                                true_value(),
                            ),
                            computes_to(
                                value_eq_call(var(left_tail), var(right_tail)),
                                true_value(),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// `cons` respects equality of its head and tail arguments.
pub fn cons_congr_theorem(
    left_head: Symbol,
    left_tail: Symbol,
    right_head: Symbol,
    right_tail: Symbol,
) -> Prop {
    forall(
        left_head,
        forall(
            left_tail,
            forall_where(
                right_head,
                equal(var(left_head), var(right_head)),
                forall_where(
                    right_tail,
                    equal(var(left_tail), var(right_tail)),
                    equal(
                        cons(var(left_head), var(left_tail)),
                        cons(var(right_head), var(right_tail)),
                    ),
                ),
            ),
        ),
    )
}

/// If `value-eq` returns true, the two values compute equally.
pub fn value_eq_sound_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            right,
            is_value(var(right)),
            implies(
                computes_to(value_eq_call(var(left), var(right)), true_value()),
                computes_to(var(left), var(right)),
            ),
        ),
    )
}

/// `value-eq` is reflexive for comparable values.
pub fn value_eq_refl_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        implies(
            computes_to(value_eq_comparable_call(var(value)), true_value()),
            computes_to(value_eq_call(var(value), var(value)), true_value()),
        ),
    )
}

/// A true `value-eq` result means the left value is comparable.
pub fn value_eq_true_implies_comparable_left_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            right,
            is_value(var(right)),
            implies(
                computes_to(value_eq_call(var(left), var(right)), true_value()),
                computes_to(value_eq_comparable_call(var(left)), true_value()),
            ),
        ),
    )
}

/// A true `value-eq` result means the right value is comparable.
pub fn value_eq_true_implies_comparable_right_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            right,
            is_value(var(right)),
            implies(
                computes_to(value_eq_call(var(left), var(right)), true_value()),
                computes_to(value_eq_comparable_call(var(right)), true_value()),
            ),
        ),
    )
}

/// `value-eq` is symmetric when it returns true.
pub fn value_eq_symm_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            right,
            is_value(var(right)),
            implies(
                computes_to(value_eq_call(var(left), var(right)), true_value()),
                computes_to(value_eq_call(var(right), var(left)), true_value()),
            ),
        ),
    )
}

/// `member` over `nil` returns false.
pub fn member_nil_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        computes_to(member_call(var(value), nil()), false_value()),
    )
}

/// If the target equals the head, `member` over a cons returns true.
pub fn member_cons_true_theorem(value: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                implies(
                    computes_to(value_eq_call(var(value), var(head)), true_value()),
                    computes_to(
                        member_call(var(value), cons(var(head), var(tail))),
                        true_value(),
                    ),
                ),
            ),
        ),
    )
}

/// If the target differs from the head, `member` recurs on the tail.
pub fn member_cons_false_theorem(value: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                implies(
                    computes_to(value_eq_call(var(value), var(head)), false_value()),
                    computes_to(
                        member_call(var(value), cons(var(head), var(tail))),
                        member_call(var(value), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// `all` over `nil` returns true.
pub fn all_nil_theorem(predicate: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        computes_to(all_call(var(predicate), nil()), true_value()),
    )
}

/// If the predicate returns true for the head, `all` recurs on the tail.
pub fn all_cons_true_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                implies(
                    computes_to(apply(var(predicate), var(head)), true_value()),
                    computes_to(
                        all_call(var(predicate), cons(var(head), var(tail))),
                        all_call(var(predicate), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// If the predicate returns false for the head, `all` over a cons returns false.
pub fn all_cons_false_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                implies(
                    computes_to(apply(var(predicate), var(head)), false_value()),
                    computes_to(
                        all_call(var(predicate), cons(var(head), var(tail))),
                        false_value(),
                    ),
                ),
            ),
        ),
    )
}

/// If the predicate returns booleans, `all` returns a boolean.
pub fn all_computes_to_bool_theorem(predicate: Symbol, value: Symbol, list: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        implies(
            forall_where(
                value,
                is_value(var(value)),
                is_bool(apply(var(predicate), var(value))),
            ),
            forall_where(
                list,
                is_list(var(list)),
                is_bool(all_call(var(predicate), var(list))),
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
    const LEFT_HEAD: Symbol = Symbol(213);
    const LEFT_TAIL: Symbol = Symbol(214);
    const RIGHT_HEAD: Symbol = Symbol(215);
    const RIGHT_TAIL: Symbol = Symbol(216);
    const LEFT_VALUE: Symbol = Symbol(217);
    const RIGHT_VALUE: Symbol = Symbol(218);
    const ZIPPED_VALUE: Symbol = Symbol(219);

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

    mod derived_shapes;
    mod evaluation;
    mod sequence_shapes;
    mod value_eq_shapes;
}
