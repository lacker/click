//! Test helpers and expected shapes for the list prelude source.

use crate::{
    Computation, LAMBDA_KIND_SYMBOL, LIST_KIND_SYMBOL, Lambda, Outcome, Proof, Prop, RUNTIME_ERROR,
    SYMBOL_KIND_SYMBOL, Symbol, Theory, absurd, and, computes_to, computes_to_list,
    elab::{proof, source::ParsedTheorem},
    equal, errors_with, exists_where, forall, forall_where, implies, is_bool, is_list, is_value,
    or, symbol_eq, value_kind,
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

pub fn take() -> Computation {
    computation_ref("take")
}

pub fn take_definition() -> Computation {
    definition("take")
}

pub fn drop() -> Computation {
    computation_ref("drop")
}

pub fn drop_definition() -> Computation {
    definition("drop")
}

pub fn split_at() -> Computation {
    computation_ref("split-at")
}

pub fn split_at_definition() -> Computation {
    definition("split-at")
}

pub fn nth() -> Computation {
    computation_ref("nth")
}

pub fn nth_definition() -> Computation {
    definition("nth")
}

pub fn replicate() -> Computation {
    computation_ref("replicate")
}

pub fn replicate_definition() -> Computation {
    definition("replicate")
}

pub fn intersperse() -> Computation {
    computation_ref("intersperse")
}

pub fn intersperse_definition() -> Computation {
    definition("intersperse")
}

pub fn intercalate() -> Computation {
    computation_ref("intercalate")
}

pub fn intercalate_definition() -> Computation {
    definition("intercalate")
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

pub fn zip() -> Computation {
    computation_ref("zip")
}

pub fn zip_definition() -> Computation {
    definition("zip")
}

pub fn unzip() -> Computation {
    computation_ref("unzip")
}

pub fn unzip_definition() -> Computation {
    definition("unzip")
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

pub fn partition() -> Computation {
    computation_ref("partition")
}

pub fn partition_definition() -> Computation {
    definition("partition")
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

pub fn find() -> Computation {
    computation_ref("find")
}

pub fn find_definition() -> Computation {
    definition("find")
}

pub fn bool_not() -> Computation {
    computation_ref("not")
}

pub fn bool_not_definition() -> Computation {
    definition("not")
}

pub fn bool_and() -> Computation {
    computation_ref("and")
}

pub fn bool_and_definition() -> Computation {
    definition("and")
}

pub fn bool_or() -> Computation {
    computation_ref("or")
}

pub fn bool_or_definition() -> Computation {
    definition("or")
}

pub fn all_lists() -> Computation {
    computation_ref("all-lists")
}

pub fn all_lists_definition() -> Computation {
    definition("all-lists")
}

pub fn none() -> Computation {
    computation_ref("none")
}

pub fn none_definition() -> Computation {
    definition("none")
}

pub fn some() -> Computation {
    computation_ref("some")
}

pub fn some_definition() -> Computation {
    definition("some")
}

pub fn is_none() -> Computation {
    computation_ref("is-none")
}

pub fn is_none_definition() -> Computation {
    definition("is-none")
}

pub fn is_some() -> Computation {
    computation_ref("is-some")
}

pub fn is_some_definition() -> Computation {
    definition("is-some")
}

pub fn option_map() -> Computation {
    computation_ref("option-map")
}

pub fn option_map_definition() -> Computation {
    definition("option-map")
}

pub fn option_bind() -> Computation {
    computation_ref("option-bind")
}

pub fn option_bind_definition() -> Computation {
    definition("option-bind")
}

pub fn unwrap_or() -> Computation {
    computation_ref("unwrap-or")
}

pub fn unwrap_or_definition() -> Computation {
    definition("unwrap-or")
}

pub fn option_filter() -> Computation {
    computation_ref("option-filter")
}

pub fn option_filter_definition() -> Computation {
    definition("option-filter")
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

pub fn elem_index() -> Computation {
    computation_ref("elem-index")
}

pub fn elem_index_definition() -> Computation {
    definition("elem-index")
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

pub fn is_pair() -> Computation {
    computation_ref("is-pair")
}

pub fn is_pair_definition() -> Computation {
    definition("is-pair")
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

pub fn nil_is_list_source_theorem() -> Prop {
    theorem_prop("nil_is_list")
}

pub fn cons_is_list_source_theorem() -> Prop {
    theorem_prop("cons_is_list")
}

pub fn cons_head_source_theorem() -> Prop {
    theorem_prop("cons_head")
}

pub fn cons_tail_source_theorem() -> Prop {
    theorem_prop("cons_tail")
}

pub fn nil_not_cons_source_theorem() -> Prop {
    theorem_prop("nil_not_cons")
}

pub fn cons_not_nil_source_theorem() -> Prop {
    theorem_prop("cons_not_nil")
}

pub fn cons_injective_head_source_theorem() -> Prop {
    theorem_prop("cons_injective_head")
}

pub fn cons_injective_tail_source_theorem() -> Prop {
    theorem_prop("cons_injective_tail")
}

pub fn cons_injective_source_theorem() -> Prop {
    theorem_prop("cons_injective")
}

pub fn list_eta_source_theorem() -> Prop {
    theorem_prop("list_eta")
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

pub fn reverse_congr_source_theorem() -> Prop {
    theorem_prop("reverse_congr")
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

pub fn map_reverse_source_theorem() -> Prop {
    theorem_prop("map_reverse")
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

pub fn member_snoc_source_theorem() -> Prop {
    theorem_prop("member_snoc")
}

pub fn tail_snoc_after_snoc_source_theorem() -> Prop {
    theorem_prop("tail_snoc_after_snoc")
}

pub fn all_lists_snoc_source_theorem() -> Prop {
    theorem_prop("all_lists_snoc")
}

pub fn concat_nil_source_theorem() -> Prop {
    theorem_prop("concat_nil")
}

pub fn concat_cons_source_theorem() -> Prop {
    theorem_prop("concat_cons")
}

pub fn concat_computes_to_list_source_theorem() -> Prop {
    theorem_prop("concat_computes_to_list")
}

pub fn concat_append_source_theorem() -> Prop {
    theorem_prop("concat_append")
}

pub fn map_length_nil_source_theorem() -> Prop {
    theorem_prop("map_length_nil")
}

pub fn map_length_cons_source_theorem() -> Prop {
    theorem_prop("map_length_cons")
}

pub fn map_length_computes_to_list_source_theorem() -> Prop {
    theorem_prop("map_length_computes_to_list")
}

pub fn length_concat_source_theorem() -> Prop {
    theorem_prop("length_concat")
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

pub fn is_pair_nil_false_source_theorem() -> Prop {
    theorem_prop("is_pair_nil_false")
}

pub fn is_pair_singleton_false_source_theorem() -> Prop {
    theorem_prop("is_pair_singleton_false")
}

pub fn is_pair_cons_cons_nil_true_source_theorem() -> Prop {
    theorem_prop("is_pair_cons_cons_nil_true")
}

pub fn is_pair_cons_cons_cons_false_source_theorem() -> Prop {
    theorem_prop("is_pair_cons_cons_cons_false")
}

pub fn is_pair_cons_cons_true_elim_source_theorem() -> Prop {
    theorem_prop("is_pair_cons_cons_true_elim")
}

pub fn is_pair_cons_true_elim_source_theorem() -> Prop {
    theorem_prop("is_pair_cons_true_elim")
}

pub fn is_pair_true_elim_source_theorem() -> Prop {
    theorem_prop("is_pair_true_elim")
}

pub fn all_is_pair_cons_true_parts_source_theorem() -> Prop {
    theorem_prop("all_is_pair_cons_true_parts")
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

pub fn append_congr_left_source_theorem() -> Prop {
    theorem_prop("append_congr_left")
}

pub fn append_congr_right_source_theorem() -> Prop {
    theorem_prop("append_congr_right")
}

pub fn append_congr_source_theorem() -> Prop {
    theorem_prop("append_congr")
}

pub fn append_assoc_source_theorem() -> Prop {
    theorem_prop("append_assoc")
}

pub fn append_take_drop_source_theorem() -> Prop {
    theorem_prop("append_take_drop")
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

pub fn append_length_singleton_source_theorem() -> Prop {
    theorem_prop("append_length_singleton")
}

pub fn length_snoc_source_theorem() -> Prop {
    theorem_prop("length_snoc")
}

pub fn length_take_source_theorem() -> Prop {
    theorem_prop("length_take")
}

pub fn length_drop_source_theorem() -> Prop {
    theorem_prop("length_drop")
}

pub fn length_take_add_length_drop_source_theorem() -> Prop {
    theorem_prop("length_take_add_length_drop")
}

pub fn length_reverse_source_theorem() -> Prop {
    theorem_prop("length_reverse")
}

pub fn take_zero_source_theorem() -> Prop {
    theorem_prop("take_zero")
}

pub fn take_nil_source_theorem() -> Prop {
    theorem_prop("take_nil")
}

pub fn take_cons_source_theorem() -> Prop {
    theorem_prop("take_cons")
}

pub fn take_computes_to_list_source_theorem() -> Prop {
    theorem_prop("take_computes_to_list")
}

pub fn take_congr_count_computation_source_theorem() -> Prop {
    theorem_prop("take_congr_count_computation")
}

pub fn take_congr_list_computation_source_theorem() -> Prop {
    theorem_prop("take_congr_list_computation")
}

pub fn drop_zero_source_theorem() -> Prop {
    theorem_prop("drop_zero")
}

pub fn drop_nil_source_theorem() -> Prop {
    theorem_prop("drop_nil")
}

pub fn drop_cons_source_theorem() -> Prop {
    theorem_prop("drop_cons")
}

pub fn drop_computes_to_list_source_theorem() -> Prop {
    theorem_prop("drop_computes_to_list")
}

pub fn drop_congr_count_computation_source_theorem() -> Prop {
    theorem_prop("drop_congr_count_computation")
}

pub fn drop_congr_list_computation_source_theorem() -> Prop {
    theorem_prop("drop_congr_list_computation")
}

pub fn take_take_source_theorem() -> Prop {
    theorem_prop("take_take")
}

pub fn drop_drop_source_theorem() -> Prop {
    theorem_prop("drop_drop")
}

pub fn take_drop_commute_source_theorem() -> Prop {
    theorem_prop("take_drop_commute")
}

pub fn split_at_def_source_theorem() -> Prop {
    theorem_prop("split_at_def")
}

pub fn split_at_zero_source_theorem() -> Prop {
    theorem_prop("split_at_zero")
}

pub fn split_at_nil_source_theorem() -> Prop {
    theorem_prop("split_at_nil")
}

pub fn split_at_cons_source_theorem() -> Prop {
    theorem_prop("split_at_cons")
}

pub fn split_at_computes_to_pair_source_theorem() -> Prop {
    theorem_prop("split_at_computes_to_pair")
}

pub fn split_at_first_take_source_theorem() -> Prop {
    theorem_prop("split_at_first_take")
}

pub fn split_at_second_drop_source_theorem() -> Prop {
    theorem_prop("split_at_second_drop")
}

pub fn nth_zero_nil_source_theorem() -> Prop {
    theorem_prop("nth_zero_nil")
}

pub fn nth_zero_cons_source_theorem() -> Prop {
    theorem_prop("nth_zero_cons")
}

pub fn nth_cons_nil_source_theorem() -> Prop {
    theorem_prop("nth_cons_nil")
}

pub fn nth_cons_cons_source_theorem() -> Prop {
    theorem_prop("nth_cons_cons")
}

pub fn nth_zero_cons_some_source_theorem() -> Prop {
    theorem_prop("nth_zero_cons_some")
}

pub fn nth_out_of_bounds_none_source_theorem() -> Prop {
    theorem_prop("nth_out_of_bounds_none")
}

pub fn nth_computes_to_option_source_theorem() -> Prop {
    theorem_prop("nth_computes_to_option")
}

pub fn replicate_zero_source_theorem() -> Prop {
    theorem_prop("replicate_zero")
}

pub fn replicate_cons_source_theorem() -> Prop {
    theorem_prop("replicate_cons")
}

pub fn replicate_computes_to_list_source_theorem() -> Prop {
    theorem_prop("replicate_computes_to_list")
}

pub fn length_replicate_source_theorem() -> Prop {
    theorem_prop("length_replicate")
}

pub fn take_replicate_source_theorem() -> Prop {
    theorem_prop("take_replicate")
}

pub fn drop_replicate_source_theorem() -> Prop {
    theorem_prop("drop_replicate")
}

pub fn intersperse_nil_source_theorem() -> Prop {
    theorem_prop("intersperse_nil")
}

pub fn intersperse_singleton_source_theorem() -> Prop {
    theorem_prop("intersperse_singleton")
}

pub fn intersperse_cons_cons_source_theorem() -> Prop {
    theorem_prop("intersperse_cons_cons")
}

pub fn intersperse_cons_computes_to_list_source_theorem() -> Prop {
    theorem_prop("intersperse_cons_computes_to_list")
}

pub fn intersperse_computes_to_list_source_theorem() -> Prop {
    theorem_prop("intersperse_computes_to_list")
}

pub fn intercalate_nil_source_theorem() -> Prop {
    theorem_prop("intercalate_nil")
}

pub fn intercalate_singleton_source_theorem() -> Prop {
    theorem_prop("intercalate_singleton")
}

pub fn intercalate_cons_cons_source_theorem() -> Prop {
    theorem_prop("intercalate_cons_cons")
}

pub fn is_list_value_true_implies_is_list_source_theorem() -> Prop {
    theorem_prop("is_list_value_true_implies_is_list")
}

pub fn value_kind_list_implies_is_list_source_theorem() -> Prop {
    theorem_prop("value_kind_list_implies_is_list")
}

pub fn is_list_implies_is_list_value_true_source_theorem() -> Prop {
    theorem_prop("is_list_implies_is_list_value_true")
}

pub fn all_lists_cons_source_theorem() -> Prop {
    theorem_prop("all_lists_cons")
}

pub fn all_lists_cons_true_source_theorem() -> Prop {
    theorem_prop("all_lists_cons_true")
}

pub fn symbol_eq_refl_source_theorem() -> Prop {
    theorem_prop("symbol_eq_refl")
}

pub fn symbol_eq_true_implies_is_symbol_left_source_theorem() -> Prop {
    theorem_prop("symbol_eq_true_implies_is_symbol_left")
}

pub fn symbol_eq_true_implies_is_symbol_right_source_theorem() -> Prop {
    theorem_prop("symbol_eq_true_implies_is_symbol_right")
}

pub fn symbol_eq_false_distinct_source_theorem() -> Prop {
    theorem_prop("symbol_eq_false_distinct")
}

pub fn symbol_eq_symm_source_theorem() -> Prop {
    theorem_prop("symbol_eq_symm")
}

pub fn symbol_eq_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("symbol_eq_computes_to_bool")
}

pub fn true_is_bool_source_theorem() -> Prop {
    theorem_prop("true_is_bool")
}

pub fn false_is_bool_source_theorem() -> Prop {
    theorem_prop("false_is_bool")
}

pub fn is_bool_elim_source_theorem() -> Prop {
    theorem_prop("is_bool_elim")
}

pub fn bool_distinct_source_theorem() -> Prop {
    theorem_prop("bool_distinct")
}

pub fn not_congr_source_theorem() -> Prop {
    theorem_prop("not_congr")
}

pub fn and_congr_left_source_theorem() -> Prop {
    theorem_prop("and_congr_left")
}

pub fn and_congr_right_source_theorem() -> Prop {
    theorem_prop("and_congr_right")
}

pub fn and_congr_source_theorem() -> Prop {
    theorem_prop("and_congr")
}

pub fn or_congr_left_source_theorem() -> Prop {
    theorem_prop("or_congr_left")
}

pub fn or_congr_right_source_theorem() -> Prop {
    theorem_prop("or_congr_right")
}

pub fn or_congr_source_theorem() -> Prop {
    theorem_prop("or_congr")
}

pub fn not_true_elim_source_theorem() -> Prop {
    theorem_prop("not_true_elim")
}

pub fn not_false_elim_source_theorem() -> Prop {
    theorem_prop("not_false_elim")
}

pub fn if_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("if_computes_to_bool")
}

pub fn if_same_source_theorem() -> Prop {
    theorem_prop("if_same")
}

pub fn if_not_source_theorem() -> Prop {
    theorem_prop("if_not")
}

pub fn if_congr_condition_source_theorem() -> Prop {
    theorem_prop("if_congr_condition")
}

pub fn if_congr_then_source_theorem() -> Prop {
    theorem_prop("if_congr_then")
}

pub fn if_congr_else_source_theorem() -> Prop {
    theorem_prop("if_congr_else")
}

pub fn if_false_result_with_true_else_source_theorem() -> Prop {
    theorem_prop("if_false_result_with_true_else")
}

pub fn if_false_result_with_error_else_source_theorem() -> Prop {
    theorem_prop("if_false_result_with_error_else")
}

pub fn if_false_result_with_false_else_source_theorem() -> Prop {
    theorem_prop("if_false_result_with_false_else")
}

pub fn if_true_result_with_true_then_source_theorem() -> Prop {
    theorem_prop("if_true_result_with_true_then")
}

pub fn if_true_result_with_true_else_source_theorem() -> Prop {
    theorem_prop("if_true_result_with_true_else")
}

pub fn if_false_result_with_false_then_source_theorem() -> Prop {
    theorem_prop("if_false_result_with_false_then")
}

pub fn and_true_intro_source_theorem() -> Prop {
    theorem_prop("and_true_intro")
}

pub fn and_true_elim_left_source_theorem() -> Prop {
    theorem_prop("and_true_elim_left")
}

pub fn and_true_elim_right_source_theorem() -> Prop {
    theorem_prop("and_true_elim_right")
}

pub fn and_false_cases_source_theorem() -> Prop {
    theorem_prop("and_false_cases")
}

pub fn or_false_intro_source_theorem() -> Prop {
    theorem_prop("or_false_intro")
}

pub fn or_false_elim_left_source_theorem() -> Prop {
    theorem_prop("or_false_elim_left")
}

pub fn or_false_elim_right_source_theorem() -> Prop {
    theorem_prop("or_false_elim_right")
}

pub fn or_true_cases_source_theorem() -> Prop {
    theorem_prop("or_true_cases")
}

pub fn and_prop_to_bool_source_theorem() -> Prop {
    theorem_prop("and_prop_to_bool")
}

pub fn and_bool_to_prop_source_theorem() -> Prop {
    theorem_prop("and_bool_to_prop")
}

pub fn or_prop_to_bool_left_source_theorem() -> Prop {
    theorem_prop("or_prop_to_bool_left")
}

pub fn or_prop_to_bool_right_source_theorem() -> Prop {
    theorem_prop("or_prop_to_bool_right")
}

pub fn or_bool_to_prop_source_theorem() -> Prop {
    theorem_prop("or_bool_to_prop")
}

pub fn not_bool_to_absurd_source_theorem() -> Prop {
    theorem_prop("not_bool_to_absurd")
}

pub fn not_absurd_to_bool_false_source_theorem() -> Prop {
    theorem_prop("not_absurd_to_bool_false")
}

pub fn and_absorb_or_source_theorem() -> Prop {
    theorem_prop("and_absorb_or")
}

pub fn or_absorb_and_source_theorem() -> Prop {
    theorem_prop("or_absorb_and")
}

pub fn and_distrib_or_left_source_theorem() -> Prop {
    theorem_prop("and_distrib_or_left")
}

pub fn and_distrib_or_right_source_theorem() -> Prop {
    theorem_prop("and_distrib_or_right")
}

pub fn or_distrib_and_left_source_theorem() -> Prop {
    theorem_prop("or_distrib_and_left")
}

pub fn or_distrib_and_right_source_theorem() -> Prop {
    theorem_prop("or_distrib_and_right")
}

pub fn not_and_source_theorem() -> Prop {
    theorem_prop("not_and")
}

pub fn not_or_source_theorem() -> Prop {
    theorem_prop("not_or")
}

pub fn none_is_none_source_theorem() -> Prop {
    theorem_prop("none_is_none")
}

pub fn some_is_none_source_theorem() -> Prop {
    theorem_prop("some_is_none")
}

pub fn none_is_some_source_theorem() -> Prop {
    theorem_prop("none_is_some")
}

pub fn some_is_some_source_theorem() -> Prop {
    theorem_prop("some_is_some")
}

pub fn some_congr_source_theorem() -> Prop {
    theorem_prop("some_congr")
}

pub fn some_injective_source_theorem() -> Prop {
    theorem_prop("some_injective")
}

pub fn option_map_none_source_theorem() -> Prop {
    theorem_prop("option_map_none")
}

pub fn option_map_some_source_theorem() -> Prop {
    theorem_prop("option_map_some")
}

pub fn option_bind_none_source_theorem() -> Prop {
    theorem_prop("option_bind_none")
}

pub fn option_bind_some_source_theorem() -> Prop {
    theorem_prop("option_bind_some")
}

pub fn unwrap_or_none_source_theorem() -> Prop {
    theorem_prop("unwrap_or_none")
}

pub fn unwrap_or_some_source_theorem() -> Prop {
    theorem_prop("unwrap_or_some")
}

pub fn option_filter_none_source_theorem() -> Prop {
    theorem_prop("option_filter_none")
}

pub fn option_filter_some_true_source_theorem() -> Prop {
    theorem_prop("option_filter_some_true")
}

pub fn option_filter_some_false_source_theorem() -> Prop {
    theorem_prop("option_filter_some_false")
}

pub fn option_map_computes_to_option_source_theorem() -> Prop {
    theorem_prop("option_map_computes_to_option")
}

pub fn option_bind_computes_to_option_source_theorem() -> Prop {
    theorem_prop("option_bind_computes_to_option")
}

pub fn unwrap_or_computes_to_value_source_theorem() -> Prop {
    theorem_prop("unwrap_or_computes_to_value")
}

pub fn option_filter_computes_to_option_source_theorem() -> Prop {
    theorem_prop("option_filter_computes_to_option")
}

pub fn option_map_identity_source_theorem() -> Prop {
    theorem_prop("option_map_identity")
}

pub fn option_map_compose_source_theorem() -> Prop {
    theorem_prop("option_map_compose")
}

pub fn option_bind_left_identity_source_theorem() -> Prop {
    theorem_prop("option_bind_left_identity")
}

pub fn option_bind_right_identity_source_theorem() -> Prop {
    theorem_prop("option_bind_right_identity")
}

pub fn option_bind_assoc_source_theorem() -> Prop {
    theorem_prop("option_bind_assoc")
}

pub fn option_map_congr_function_source_theorem() -> Prop {
    theorem_prop("option_map_congr_function")
}

pub fn option_map_congr_option_source_theorem() -> Prop {
    theorem_prop("option_map_congr_option")
}

pub fn option_map_congr_option_computation_source_theorem() -> Prop {
    theorem_prop("option_map_congr_option_computation")
}

pub fn option_map_congr_source_theorem() -> Prop {
    theorem_prop("option_map_congr")
}

pub fn option_bind_congr_function_source_theorem() -> Prop {
    theorem_prop("option_bind_congr_function")
}

pub fn option_bind_congr_option_source_theorem() -> Prop {
    theorem_prop("option_bind_congr_option")
}

pub fn option_bind_congr_option_computation_source_theorem() -> Prop {
    theorem_prop("option_bind_congr_option_computation")
}

pub fn unwrap_or_congr_default_source_theorem() -> Prop {
    theorem_prop("unwrap_or_congr_default")
}

pub fn unwrap_or_congr_option_source_theorem() -> Prop {
    theorem_prop("unwrap_or_congr_option")
}

pub fn pair_first_source_theorem() -> Prop {
    theorem_prop("pair_first")
}

pub fn pair_tail_source_theorem() -> Prop {
    theorem_prop("pair_tail")
}

pub fn pair_second_source_theorem() -> Prop {
    theorem_prop("pair_second")
}

pub fn pair_computes_to_list_source_theorem() -> Prop {
    theorem_prop("pair_computes_to_list")
}

pub fn pair_computes_to_value_source_theorem() -> Prop {
    theorem_prop("pair_computes_to_value")
}

pub fn pair_eta_source_theorem() -> Prop {
    theorem_prop("pair_eta")
}

pub fn pair_congr_source_theorem() -> Prop {
    theorem_prop("pair_congr")
}

pub fn pair_first_from_computation_source_theorem() -> Prop {
    theorem_prop("pair_first_from_computation")
}

pub fn pair_second_from_computation_source_theorem() -> Prop {
    theorem_prop("pair_second_from_computation")
}

pub fn pair_injective_first_source_theorem() -> Prop {
    theorem_prop("pair_injective_first")
}

pub fn pair_injective_second_source_theorem() -> Prop {
    theorem_prop("pair_injective_second")
}

pub fn pair_injective_source_theorem() -> Prop {
    theorem_prop("pair_injective")
}

pub fn list_pair_first_from_computation_source_theorem() -> Prop {
    theorem_prop("list_pair_first_from_computation")
}

pub fn list_pair_second_from_computation_source_theorem() -> Prop {
    theorem_prop("list_pair_second_from_computation")
}

pub fn intercalate_cons_computes_to_list_source_theorem() -> Prop {
    theorem_prop("intercalate_cons_computes_to_list")
}

pub fn intercalate_computes_to_list_source_theorem() -> Prop {
    theorem_prop("intercalate_computes_to_list")
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

pub fn map_replicate_source_theorem() -> Prop {
    theorem_prop("map_replicate")
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

pub fn fold_right_congr_source_theorem() -> Prop {
    theorem_prop("fold_right_congr")
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

pub fn fold_left_congr_source_theorem() -> Prop {
    theorem_prop("fold_left_congr")
}

pub fn zip_left_nil_source_theorem() -> Prop {
    theorem_prop("zip_left_nil")
}

pub fn zip_right_nil_source_theorem() -> Prop {
    theorem_prop("zip_right_nil")
}

pub fn zip_cons_source_theorem() -> Prop {
    theorem_prop("zip_cons")
}

pub fn zip_computes_to_list_source_theorem() -> Prop {
    theorem_prop("zip_computes_to_list")
}

pub fn zip_pair_shape_source_theorem() -> Prop {
    theorem_prop("zip_pair_shape")
}

pub fn unzip_nil_source_theorem() -> Prop {
    theorem_prop("unzip_nil")
}

pub fn unzip_cons_source_theorem() -> Prop {
    theorem_prop("unzip_cons")
}

pub fn unzip_pair_shape_source_theorem() -> Prop {
    theorem_prop("unzip_pair_shape")
}

pub fn zip_unzip_source_theorem() -> Prop {
    theorem_prop("zip_unzip")
}

pub fn unzip_zip_source_theorem() -> Prop {
    theorem_prop("unzip_zip")
}

pub fn zip_with_as_map_zip_source_theorem() -> Prop {
    theorem_prop("zip_with_as_map_zip")
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

pub fn filter_congr_source_theorem() -> Prop {
    theorem_prop("filter_congr")
}

pub fn reject_nil_source_theorem() -> Prop {
    theorem_prop("reject_nil")
}

pub fn reject_cons_true_source_theorem() -> Prop {
    theorem_prop("reject_cons_true")
}

pub fn reject_cons_false_source_theorem() -> Prop {
    theorem_prop("reject_cons_false")
}

pub fn reject_computes_to_list_source_theorem() -> Prop {
    theorem_prop("reject_computes_to_list")
}

pub fn filter_append_source_theorem() -> Prop {
    theorem_prop("filter_append")
}

pub fn reject_append_source_theorem() -> Prop {
    theorem_prop("reject_append")
}

pub fn filter_idempotent_source_theorem() -> Prop {
    theorem_prop("filter_idempotent")
}

pub fn reject_idempotent_source_theorem() -> Prop {
    theorem_prop("reject_idempotent")
}

pub fn partition_nil_source_theorem() -> Prop {
    theorem_prop("partition_nil")
}

pub fn partition_cons_true_source_theorem() -> Prop {
    theorem_prop("partition_cons_true")
}

pub fn partition_cons_false_source_theorem() -> Prop {
    theorem_prop("partition_cons_false")
}

pub fn partition_computes_to_pair_source_theorem() -> Prop {
    theorem_prop("partition_computes_to_pair")
}

pub fn partition_first_filter_source_theorem() -> Prop {
    theorem_prop("partition_first_filter")
}

pub fn partition_second_filter_false_source_theorem() -> Prop {
    theorem_prop("partition_second_filter_false")
}

pub fn partition_second_reject_source_theorem() -> Prop {
    theorem_prop("partition_second_reject")
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

pub fn any_append_source_theorem() -> Prop {
    theorem_prop("any_append")
}

pub fn all_true_implies_not_any_false_source_theorem() -> Prop {
    theorem_prop("all_true_implies_not_any_false")
}

pub fn any_true_implies_not_all_false_source_theorem() -> Prop {
    theorem_prop("any_true_implies_not_all_false")
}

pub fn find_nil_source_theorem() -> Prop {
    theorem_prop("find_nil")
}

pub fn find_cons_true_source_theorem() -> Prop {
    theorem_prop("find_cons_true")
}

pub fn find_cons_false_source_theorem() -> Prop {
    theorem_prop("find_cons_false")
}

pub fn find_append_source_theorem() -> Prop {
    theorem_prop("find_append")
}

pub fn elem_index_nil_source_theorem() -> Prop {
    theorem_prop("elem_index_nil")
}

pub fn elem_index_cons_true_source_theorem() -> Prop {
    theorem_prop("elem_index_cons_true")
}

pub fn elem_index_cons_false_none_source_theorem() -> Prop {
    theorem_prop("elem_index_cons_false_none")
}

pub fn elem_index_cons_false_some_source_theorem() -> Prop {
    theorem_prop("elem_index_cons_false_some")
}

pub fn elem_index_cons_some_cases_source_theorem() -> Prop {
    theorem_prop("elem_index_cons_some_cases")
}

pub fn elem_index_append_left_source_theorem() -> Prop {
    theorem_prop("elem_index_append_left")
}

pub fn elem_index_cons_none_parts_source_theorem() -> Prop {
    theorem_prop("elem_index_cons_none_parts")
}

pub fn elem_index_append_right_source_theorem() -> Prop {
    theorem_prop("elem_index_append_right")
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

pub fn is_symbol_true_implies_is_list_value_false_source_theorem() -> Prop {
    theorem_prop("is_symbol_true_implies_is_list_value_false")
}

pub fn is_lambda_true_implies_is_symbol_false_source_theorem() -> Prop {
    theorem_prop("is_lambda_true_implies_is_symbol_false")
}

pub fn is_lambda_true_implies_is_list_value_false_source_theorem() -> Prop {
    theorem_prop("is_lambda_true_implies_is_list_value_false")
}

pub fn is_list_value_true_implies_is_symbol_false_source_theorem() -> Prop {
    theorem_prop("is_list_value_true_implies_is_symbol_false")
}

pub fn is_list_value_true_implies_is_lambda_false_source_theorem() -> Prop {
    theorem_prop("is_list_value_true_implies_is_lambda_false")
}

pub fn value_kind_exactly_one_source_theorem() -> Prop {
    theorem_prop("value_kind_exactly_one")
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

pub fn value_eq_comparable_no_lambdas_source_theorem() -> Prop {
    theorem_prop("value_eq_comparable_no_lambdas")
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

pub fn value_eq_cons_false_cases_source_theorem() -> Prop {
    theorem_prop("value_eq_cons_false_cases")
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

pub fn value_eq_trans_source_theorem() -> Prop {
    theorem_prop("value_eq_trans")
}

pub fn value_eq_complete_for_comparable_values_source_theorem() -> Prop {
    theorem_prop("value_eq_complete_for_comparable_values")
}

pub fn value_eq_false_implies_not_equal_for_comparable_values_source_theorem() -> Prop {
    theorem_prop("value_eq_false_implies_not_equal_for_comparable_values")
}

pub fn symbol_not_list_source_theorem() -> Prop {
    theorem_prop("symbol_not_list")
}

pub fn symbol_not_lambda_source_theorem() -> Prop {
    theorem_prop("symbol_not_lambda")
}

pub fn list_not_lambda_source_theorem() -> Prop {
    theorem_prop("list_not_lambda")
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

pub fn member_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("member_computes_to_bool")
}

pub fn member_is_bool_for_comparable_value_source_theorem() -> Prop {
    theorem_prop("member_is_bool_for_comparable_value")
}

pub fn member_cons_or_source_theorem() -> Prop {
    theorem_prop("member_cons_or")
}

pub fn member_append_source_theorem() -> Prop {
    theorem_prop("member_append")
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

pub fn all_cons_true_parts_source_theorem() -> Prop {
    theorem_prop("all_cons_true_parts")
}

pub fn all_append_source_theorem() -> Prop {
    theorem_prop("all_append")
}

pub fn map_identity_source_theorem() -> Prop {
    theorem_prop("map_identity")
}

pub fn map_compose_source_theorem() -> Prop {
    theorem_prop("map_compose")
}

pub fn map_congr_source_theorem() -> Prop {
    theorem_prop("map_congr")
}

pub fn map_append_source_theorem() -> Prop {
    theorem_prop("map_append")
}

pub fn map_snoc_source_theorem() -> Prop {
    theorem_prop("map_snoc")
}

pub fn map_take_source_theorem() -> Prop {
    theorem_prop("map_take")
}

pub fn map_drop_source_theorem() -> Prop {
    theorem_prop("map_drop")
}

pub fn option_map_nth_source_theorem() -> Prop {
    theorem_prop("option_map_nth")
}

pub fn option_map_find_source_theorem() -> Prop {
    theorem_prop("option_map_find")
}

pub fn option_bind_find_none_source_theorem() -> Prop {
    theorem_prop("option_bind_find_none")
}

pub fn option_bind_find_some_source_theorem() -> Prop {
    theorem_prop("option_bind_find_some")
}

pub fn concat_map_singleton_source_theorem() -> Prop {
    theorem_prop("concat_map_singleton")
}

pub fn concat_map_append_source_theorem() -> Prop {
    theorem_prop("concat_map_append")
}

pub fn concat_map_as_concat_map_source_theorem() -> Prop {
    theorem_prop("concat_map_as_concat_map")
}

pub fn fold_right_cons_nil_source_theorem() -> Prop {
    theorem_prop("fold_right_cons_nil")
}

pub fn fold_right_append_source_theorem() -> Prop {
    theorem_prop("fold_right_append")
}

pub fn fold_left_append_source_theorem() -> Prop {
    theorem_prop("fold_left_append")
}

pub fn fold_right_map_source_theorem() -> Prop {
    theorem_prop("fold_right_map")
}

pub fn fold_left_map_source_theorem() -> Prop {
    theorem_prop("fold_left_map")
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

pub fn take_call(count: Computation, list: Computation) -> Computation {
    apply(apply(take(), count), list)
}

pub fn drop_call(count: Computation, list: Computation) -> Computation {
    apply(apply(drop(), count), list)
}

pub fn split_at_call(count: Computation, list: Computation) -> Computation {
    apply(apply(split_at(), count), list)
}

pub fn nth_call(index: Computation, list: Computation) -> Computation {
    apply(apply(nth(), index), list)
}

pub fn replicate_call(count: Computation, value: Computation) -> Computation {
    apply(apply(replicate(), count), value)
}

pub fn intersperse_call(separator: Computation, list: Computation) -> Computation {
    apply(apply(intersperse(), separator), list)
}

pub fn intercalate_call(separator: Computation, lists: Computation) -> Computation {
    apply(apply(intercalate(), separator), lists)
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

pub fn zip_call(left: Computation, right: Computation) -> Computation {
    apply(apply(zip(), left), right)
}

pub fn unzip_call(pairs: Computation) -> Computation {
    apply(unzip(), pairs)
}

pub fn zip_with_call(function: Computation, left: Computation, right: Computation) -> Computation {
    apply(apply(apply(zip_with(), function), left), right)
}

pub fn filter_call(predicate: Computation, list: Computation) -> Computation {
    apply(apply(filter(), predicate), list)
}

pub fn partition_call(predicate: Computation, list: Computation) -> Computation {
    apply(apply(partition(), predicate), list)
}

pub fn any_call(predicate: Computation, list: Computation) -> Computation {
    apply(apply(any(), predicate), list)
}

pub fn all_call(predicate: Computation, list: Computation) -> Computation {
    apply(apply(all(), predicate), list)
}

pub fn find_call(predicate: Computation, list: Computation) -> Computation {
    apply(apply(find(), predicate), list)
}

pub fn bool_not_call(value: Computation) -> Computation {
    apply(bool_not(), value)
}

pub fn bool_and_call(left: Computation, right: Computation) -> Computation {
    apply(apply(bool_and(), left), right)
}

pub fn bool_or_call(left: Computation, right: Computation) -> Computation {
    apply(apply(bool_or(), left), right)
}

pub fn all_lists_call(lists: Computation) -> Computation {
    apply(all_lists(), lists)
}

pub fn some_call(value: Computation) -> Computation {
    apply(some(), value)
}

pub fn is_none_call(option: Computation) -> Computation {
    apply(is_none(), option)
}

pub fn is_some_call(option: Computation) -> Computation {
    apply(is_some(), option)
}

pub fn option_map_call(function: Computation, option: Computation) -> Computation {
    apply(apply(option_map(), function), option)
}

pub fn option_bind_call(function: Computation, option: Computation) -> Computation {
    apply(apply(option_bind(), function), option)
}

pub fn unwrap_or_call(default: Computation, option: Computation) -> Computation {
    apply(apply(unwrap_or(), default), option)
}

pub fn option_filter_call(predicate: Computation, option: Computation) -> Computation {
    apply(apply(option_filter(), predicate), option)
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

pub fn elem_index_call(value: Computation, list: Computation) -> Computation {
    apply(apply(elem_index(), value), list)
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

pub fn is_pair_call(value: Computation) -> Computation {
    apply(is_pair(), value)
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

/// `is-pair(nil)` returns `:false`.
pub fn is_pair_nil_false_theorem() -> Prop {
    computes_to(is_pair_call(nil()), false_value())
}

/// `is-pair` returns `:false` for a one-element list.
pub fn is_pair_singleton_false_theorem(head: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        computes_to(is_pair_call(singleton(var(head))), false_value()),
    )
}

/// `is-pair` returns `:true` for a two-element list.
pub fn is_pair_cons_cons_nil_true_theorem(first: Symbol, second: Symbol) -> Prop {
    forall_where(
        first,
        is_value(var(first)),
        forall_where(
            second,
            is_value(var(second)),
            computes_to(is_pair_call(pair(var(first), var(second))), true_value()),
        ),
    )
}

/// `is-pair` returns `:false` for lists with at least three elements.
pub fn is_pair_cons_cons_cons_false_theorem(
    first: Symbol,
    second: Symbol,
    third: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        first,
        is_value(var(first)),
        forall_where(
            second,
            is_value(var(second)),
            forall_where(
                third,
                is_value(var(third)),
                forall_where(
                    tail,
                    is_list(var(tail)),
                    computes_to(
                        is_pair_call(cons(
                            var(first),
                            cons(var(second), cons(var(third), var(tail))),
                        )),
                        false_value(),
                    ),
                ),
            ),
        ),
    )
}

/// If a two-or-more element list is an `is-pair`, its tail after the second
/// element is `nil`.
pub fn is_pair_cons_cons_true_elim_theorem(first: Symbol, second: Symbol, rest: Symbol) -> Prop {
    forall_where(
        first,
        is_value(var(first)),
        forall_where(
            second,
            is_value(var(second)),
            forall_where(
                rest,
                is_list(var(rest)),
                implies(
                    computes_to(
                        is_pair_call(cons(var(first), cons(var(second), var(rest)))),
                        true_value(),
                    ),
                    computes_to(var(rest), nil()),
                ),
            ),
        ),
    )
}

/// If a cons value is an `is-pair`, its tail is a singleton.
pub fn is_pair_cons_true_elim_theorem(first: Symbol, tail: Symbol, second: Symbol) -> Prop {
    forall_where(
        first,
        is_value(var(first)),
        forall_where(
            tail,
            is_list(var(tail)),
            implies(
                computes_to(is_pair_call(cons(var(first), var(tail))), true_value()),
                exists_where(
                    second,
                    is_value(var(second)),
                    computes_to(var(tail), singleton(var(second))),
                ),
            ),
        ),
    )
}

/// If an arbitrary value is an `is-pair`, it computes to a two-element list.
pub fn is_pair_true_elim_theorem(value: Symbol, first: Symbol, second: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        implies(
            computes_to(is_pair_call(var(value)), true_value()),
            exists_where(
                first,
                is_value(var(first)),
                exists_where(
                    second,
                    is_value(var(second)),
                    computes_to(var(value), pair(var(first), var(second))),
                ),
            ),
        ),
    )
}

/// If `all is-pair` is true for a cons, it is true for the head and tail
/// pieces separately.
pub fn all_is_pair_cons_true_parts_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            implies(
                computes_to(
                    all_call(is_pair(), cons(var(head), var(tail))),
                    true_value(),
                ),
                and(
                    computes_to(is_pair_call(var(head)), true_value()),
                    computes_to(all_call(is_pair(), var(tail)), true_value()),
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

/// Taking a zero-length prefix returns `nil`.
pub fn take_zero_theorem(list: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to(take_call(nil(), var(list)), nil()),
    )
}

/// Taking from `nil` returns `nil`.
pub fn take_nil_theorem(count: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        computes_to(take_call(var(count), nil()), nil()),
    )
}

/// Taking a cons count from a cons list preserves the list head and recurs on
/// both tails.
pub fn take_cons_theorem(
    count_head: Symbol,
    count_tail: Symbol,
    head: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        count_head,
        is_value(var(count_head)),
        forall_where(
            count_tail,
            is_list(var(count_tail)),
            forall_where(
                head,
                is_value(var(head)),
                forall_where(
                    tail,
                    is_list(var(tail)),
                    computes_to(
                        take_call(
                            cons(var(count_head), var(count_tail)),
                            cons(var(head), var(tail)),
                        ),
                        cons(var(head), take_call(var(count_tail), var(tail))),
                    ),
                ),
            ),
        ),
    )
}

/// If the count and input are lists, then `take` computes to a list.
pub fn take_computes_to_list_theorem(count: Symbol, list: Symbol, result: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to_list(result, take_call(var(count), var(list))),
        ),
    )
}

/// Replacing a count computation by its list result preserves `take`.
pub fn take_congr_count_computation_theorem(
    count: Symbol,
    count_value: Symbol,
    list: Symbol,
) -> Prop {
    forall(
        count,
        forall_where(
            count_value,
            is_list(var(count_value)),
            implies(
                computes_to(var(count), var(count_value)),
                forall_where(
                    list,
                    is_list(var(list)),
                    computes_to(
                        take_call(var(count), var(list)),
                        take_call(var(count_value), var(list)),
                    ),
                ),
            ),
        ),
    )
}

/// Replacing a list computation by its list result preserves `take`.
pub fn take_congr_list_computation_theorem(
    count: Symbol,
    list: Symbol,
    list_value: Symbol,
) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall(
            list,
            forall_where(
                list_value,
                is_list(var(list_value)),
                implies(
                    computes_to(var(list), var(list_value)),
                    computes_to(
                        take_call(var(count), var(list)),
                        take_call(var(count), var(list_value)),
                    ),
                ),
            ),
        ),
    )
}

/// Dropping zero elements returns the input list.
pub fn drop_zero_theorem(list: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to(drop_call(nil(), var(list)), var(list)),
    )
}

/// Dropping from `nil` returns `nil`.
pub fn drop_nil_theorem(count: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        computes_to(drop_call(var(count), nil()), nil()),
    )
}

/// Dropping a cons count from a cons list recurs on both tails.
pub fn drop_cons_theorem(
    count_head: Symbol,
    count_tail: Symbol,
    head: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        count_head,
        is_value(var(count_head)),
        forall_where(
            count_tail,
            is_list(var(count_tail)),
            forall_where(
                head,
                is_value(var(head)),
                forall_where(
                    tail,
                    is_list(var(tail)),
                    computes_to(
                        drop_call(
                            cons(var(count_head), var(count_tail)),
                            cons(var(head), var(tail)),
                        ),
                        drop_call(var(count_tail), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// If the count and input are lists, then `drop` computes to a list.
pub fn drop_computes_to_list_theorem(count: Symbol, list: Symbol, result: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to_list(result, drop_call(var(count), var(list))),
        ),
    )
}

/// Replacing a count computation by its list result preserves `drop`.
pub fn drop_congr_count_computation_theorem(
    count: Symbol,
    count_value: Symbol,
    list: Symbol,
) -> Prop {
    forall(
        count,
        forall_where(
            count_value,
            is_list(var(count_value)),
            implies(
                computes_to(var(count), var(count_value)),
                forall_where(
                    list,
                    is_list(var(list)),
                    computes_to(
                        drop_call(var(count), var(list)),
                        drop_call(var(count_value), var(list)),
                    ),
                ),
            ),
        ),
    )
}

/// Replacing a list computation by its list result preserves `drop`.
pub fn drop_congr_list_computation_theorem(
    count: Symbol,
    list: Symbol,
    list_value: Symbol,
) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall(
            list,
            forall_where(
                list_value,
                is_list(var(list_value)),
                implies(
                    computes_to(var(list), var(list_value)),
                    computes_to(
                        drop_call(var(count), var(list)),
                        drop_call(var(count), var(list_value)),
                    ),
                ),
            ),
        ),
    )
}

/// Taking the same count twice is idempotent.
pub fn take_take_theorem(count: Symbol, list: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to(
                take_call(var(count), take_call(var(count), var(list))),
                take_call(var(count), var(list)),
            ),
        ),
    )
}

/// Dropping `left` and then `right` is dropping `append(left, right)`.
pub fn drop_drop_theorem(left: Symbol, right: Symbol, list: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        forall_where(
            right,
            is_list(var(right)),
            forall_where(
                list,
                is_list(var(list)),
                computes_to(
                    drop_call(var(right), drop_call(var(left), var(list))),
                    drop_call(append_call(var(left), var(right)), var(list)),
                ),
            ),
        ),
    )
}

/// Taking after dropping equals dropping after taking the combined prefix.
pub fn take_drop_commute_theorem(take_count: Symbol, drop_count: Symbol, list: Symbol) -> Prop {
    forall_where(
        take_count,
        is_list(var(take_count)),
        forall_where(
            drop_count,
            is_list(var(drop_count)),
            forall_where(
                list,
                is_list(var(list)),
                computes_to(
                    take_call(var(take_count), drop_call(var(drop_count), var(list))),
                    drop_call(
                        var(drop_count),
                        take_call(append_call(var(drop_count), var(take_count)), var(list)),
                    ),
                ),
            ),
        ),
    )
}

/// Splitting is definitionally the pair of `take` and `drop`.
pub fn split_at_def_theorem(count: Symbol, list: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to(
                split_at_call(var(count), var(list)),
                pair(
                    take_call(var(count), var(list)),
                    drop_call(var(count), var(list)),
                ),
            ),
        ),
    )
}

/// Splitting at zero returns an empty prefix and the full suffix.
pub fn split_at_zero_theorem(list: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        computes_to(split_at_call(nil(), var(list)), pair(nil(), var(list))),
    )
}

/// Splitting `nil` returns two empty lists.
pub fn split_at_nil_theorem(count: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        computes_to(split_at_call(var(count), nil()), pair(nil(), nil())),
    )
}

/// Splitting cons count and cons list puts the head in the prefix and recurs on
/// the tails through `take` and `drop`.
pub fn split_at_cons_theorem(
    count_head: Symbol,
    count_tail: Symbol,
    head: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        count_head,
        is_value(var(count_head)),
        forall_where(
            count_tail,
            is_list(var(count_tail)),
            forall_where(
                head,
                is_value(var(head)),
                forall_where(
                    tail,
                    is_list(var(tail)),
                    computes_to(
                        split_at_call(
                            cons(var(count_head), var(count_tail)),
                            cons(var(head), var(tail)),
                        ),
                        pair(
                            cons(var(head), take_call(var(count_tail), var(tail))),
                            drop_call(var(count_tail), var(tail)),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Indexing into `nil` with zero returns `none`.
pub fn nth_zero_nil_theorem() -> Prop {
    computes_to(nth_call(nil(), nil()), none())
}

/// Indexing zero into a cons returns `some` of the head.
pub fn nth_zero_cons_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            computes_to(
                nth_call(nil(), cons(var(head), var(tail))),
                some_call(var(head)),
            ),
        ),
    )
}

/// Indexing into `nil` with a cons index returns `none`.
pub fn nth_cons_nil_theorem(index_head: Symbol, index_tail: Symbol) -> Prop {
    forall_where(
        index_head,
        is_value(var(index_head)),
        forall_where(
            index_tail,
            is_list(var(index_tail)),
            computes_to(
                nth_call(cons(var(index_head), var(index_tail)), nil()),
                none(),
            ),
        ),
    )
}

/// Indexing with a cons index into a cons list recurs on both tails.
pub fn nth_cons_cons_theorem(
    index_head: Symbol,
    index_tail: Symbol,
    head: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        index_head,
        is_value(var(index_head)),
        forall_where(
            index_tail,
            is_list(var(index_tail)),
            forall_where(
                head,
                is_value(var(head)),
                forall_where(
                    tail,
                    is_list(var(tail)),
                    computes_to(
                        nth_call(
                            cons(var(index_head), var(index_tail)),
                            cons(var(head), var(tail)),
                        ),
                        nth_call(var(index_tail), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// Replicating a value zero times returns `nil`.
pub fn replicate_zero_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        computes_to(replicate_call(nil(), var(value)), nil()),
    )
}

/// Replicating with a cons count preserves the value and recurs on the count
/// tail.
pub fn replicate_cons_theorem(count_head: Symbol, count_tail: Symbol, value: Symbol) -> Prop {
    forall_where(
        count_head,
        is_value(var(count_head)),
        forall_where(
            count_tail,
            is_list(var(count_tail)),
            forall_where(
                value,
                is_value(var(value)),
                computes_to(
                    replicate_call(cons(var(count_head), var(count_tail)), var(value)),
                    cons(var(value), replicate_call(var(count_tail), var(value))),
                ),
            ),
        ),
    )
}

/// If the count is a list and the element is a value, then `replicate`
/// computes to a list.
pub fn replicate_computes_to_list_theorem(count: Symbol, value: Symbol, result: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            value,
            is_value(var(value)),
            computes_to_list(result, replicate_call(var(count), var(value))),
        ),
    )
}

/// The length of a replicated list is the length of the count list.
pub fn length_replicate_theorem(count: Symbol, value: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            value,
            is_value(var(value)),
            computes_to(
                length_call(replicate_call(var(count), var(value))),
                length_call(var(count)),
            ),
        ),
    )
}

/// Taking the full replicated count returns the replicated list.
pub fn take_replicate_theorem(count: Symbol, value: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            value,
            is_value(var(value)),
            computes_to(
                take_call(var(count), replicate_call(var(count), var(value))),
                replicate_call(var(count), var(value)),
            ),
        ),
    )
}

/// Dropping the full replicated count returns `nil`.
pub fn drop_replicate_theorem(count: Symbol, value: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            value,
            is_value(var(value)),
            computes_to(
                drop_call(var(count), replicate_call(var(count), var(value))),
                nil(),
            ),
        ),
    )
}

/// Interspersing into an empty list returns `nil`.
pub fn intersperse_nil_theorem(separator: Symbol) -> Prop {
    forall_where(
        separator,
        is_value(var(separator)),
        computes_to(intersperse_call(var(separator), nil()), nil()),
    )
}

/// Interspersing into a singleton list leaves it unchanged.
pub fn intersperse_singleton_theorem(separator: Symbol, head: Symbol) -> Prop {
    forall_where(
        separator,
        is_value(var(separator)),
        forall_where(
            head,
            is_value(var(head)),
            computes_to(
                intersperse_call(var(separator), singleton(var(head))),
                singleton(var(head)),
            ),
        ),
    )
}

/// Interspersing into a list with at least two elements keeps the head,
/// inserts the separator, and recurs on the tail.
pub fn intersperse_cons_cons_theorem(
    separator: Symbol,
    head: Symbol,
    next: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        separator,
        is_value(var(separator)),
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
                        intersperse_call(
                            var(separator),
                            cons(var(head), cons(var(next), var(tail))),
                        ),
                        cons(
                            var(head),
                            cons(
                                var(separator),
                                intersperse_call(var(separator), cons(var(next), var(tail))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// If the tail is a list, the head and separator are values, then
/// `intersperse` computes to a list on a cons input.
pub fn intersperse_cons_computes_to_list_theorem(
    separator: Symbol,
    tail: Symbol,
    head: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        separator,
        is_value(var(separator)),
        forall_where(
            tail,
            is_list(var(tail)),
            forall_where(
                head,
                is_value(var(head)),
                computes_to_list(
                    result,
                    intersperse_call(var(separator), cons(var(head), var(tail))),
                ),
            ),
        ),
    )
}

/// If the input is a list and the separator is a value, then `intersperse`
/// computes to a list.
pub fn intersperse_computes_to_list_theorem(
    separator: Symbol,
    list: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        separator,
        is_value(var(separator)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to_list(result, intersperse_call(var(separator), var(list))),
        ),
    )
}

/// Intercalating an empty list of lists returns `nil`.
pub fn intercalate_nil_theorem(separator: Symbol) -> Prop {
    forall_where(
        separator,
        is_list(var(separator)),
        computes_to(intercalate_call(var(separator), nil()), nil()),
    )
}

/// Intercalating a singleton list of lists returns the only list.
pub fn intercalate_singleton_theorem(separator: Symbol, list: Symbol) -> Prop {
    forall_where(
        separator,
        is_list(var(separator)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to(
                intercalate_call(var(separator), singleton(var(list))),
                var(list),
            ),
        ),
    )
}

/// Intercalating a list with at least two elements appends the head list, the
/// separator list, and then recurs on the tail.
pub fn intercalate_cons_cons_theorem(
    separator: Symbol,
    head: Symbol,
    next: Symbol,
    tail: Symbol,
) -> Prop {
    forall_where(
        separator,
        is_list(var(separator)),
        forall_where(
            head,
            is_list(var(head)),
            forall_where(
                next,
                is_list(var(next)),
                forall_where(
                    tail,
                    is_list(var(tail)),
                    computes_to(
                        intercalate_call(
                            var(separator),
                            cons(var(head), cons(var(next), var(tail))),
                        ),
                        append_call(
                            var(head),
                            append_call(
                                var(separator),
                                intercalate_call(var(separator), cons(var(next), var(tail))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// A value whose list-kind predicate returns true is a list.
pub fn is_list_value_true_implies_is_list_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        implies(
            computes_to(is_list_value_call(var(value)), true_value()),
            is_list(var(value)),
        ),
    )
}

/// If `all-lists` returns true on a cons, then the head is a list and the
/// tail also satisfies `all-lists`.
pub fn all_lists_cons_true_theorem(head: Symbol, tail: Symbol) -> Prop {
    forall_where(
        head,
        is_value(var(head)),
        forall_where(
            tail,
            is_list(var(tail)),
            implies(
                computes_to(all_lists_call(cons(var(head), var(tail))), true_value()),
                and(
                    is_list(var(head)),
                    computes_to(all_lists_call(var(tail)), true_value()),
                ),
            ),
        ),
    )
}

/// `none` is recognized as none.
pub fn none_is_none_theorem() -> Prop {
    computes_to(is_none_call(none()), true_value())
}

/// `some value` is not none.
pub fn some_is_none_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        computes_to(is_none_call(some_call(var(value))), false_value()),
    )
}

/// `none` is not some.
pub fn none_is_some_theorem() -> Prop {
    computes_to(is_some_call(none()), false_value())
}

/// `some value` is recognized as some.
pub fn some_is_some_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        computes_to(is_some_call(some_call(var(value))), true_value()),
    )
}

/// If a cons input satisfies `all-lists`, then `intercalate` computes to a
/// list on that cons input.
pub fn intercalate_cons_computes_to_list_theorem(
    separator: Symbol,
    tail: Symbol,
    head: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        separator,
        is_list(var(separator)),
        forall_where(
            tail,
            is_list(var(tail)),
            forall_where(
                head,
                is_value(var(head)),
                implies(
                    computes_to(all_lists_call(cons(var(head), var(tail))), true_value()),
                    computes_to_list(
                        result,
                        intercalate_call(var(separator), cons(var(head), var(tail))),
                    ),
                ),
            ),
        ),
    )
}

/// If the separator is a list and the input list contains only lists, then
/// `intercalate` computes to a list.
pub fn intercalate_computes_to_list_theorem(
    separator: Symbol,
    lists: Symbol,
    result: Symbol,
) -> Prop {
    forall_where(
        separator,
        is_list(var(separator)),
        forall_where(
            lists,
            is_list(var(lists)),
            implies(
                computes_to(all_lists_call(var(lists)), true_value()),
                computes_to_list(result, intercalate_call(var(separator), var(lists))),
            ),
        ),
    )
}

/// Appending the prefix taken by a count to the suffix dropped by that count
/// rebuilds the original list.
pub fn append_take_drop_theorem(count: Symbol, list: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to(
                append_call(
                    take_call(var(count), var(list)),
                    drop_call(var(count), var(list)),
                ),
                var(list),
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

/// Snoc increases a list's length by one.
pub fn length_snoc_theorem(list: Symbol, value: Symbol) -> Prop {
    forall_where(
        list,
        is_list(var(list)),
        forall_where(
            value,
            is_value(var(value)),
            computes_to(
                length_call(snoc_call(var(list), var(value))),
                cons(unit(), length_call(var(list))),
            ),
        ),
    )
}

/// The length of a taken prefix is the corresponding prefix of the length.
pub fn length_take_theorem(count: Symbol, list: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to(
                length_call(take_call(var(count), var(list))),
                take_call(var(count), length_call(var(list))),
            ),
        ),
    )
}

/// The length of a dropped suffix is the corresponding suffix of the length.
pub fn length_drop_theorem(count: Symbol, list: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to(
                length_call(drop_call(var(count), var(list))),
                drop_call(var(count), length_call(var(list))),
            ),
        ),
    )
}

/// The lengths of `take` and `drop` append back to the original length.
pub fn length_take_add_length_drop_theorem(count: Symbol, list: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        forall_where(
            list,
            is_list(var(list)),
            computes_to(
                append_call(
                    length_call(take_call(var(count), var(list))),
                    length_call(drop_call(var(count), var(list))),
                ),
                length_call(var(list)),
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

/// Mapping over `replicate` maps the replicated value.
pub fn map_replicate_theorem(
    function: Symbol,
    value: Symbol,
    mapped_value: Symbol,
    count: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            value,
            is_value(var(value)),
            forall_where(
                mapped_value,
                is_value(var(mapped_value)),
                implies(
                    computes_to(apply(var(function), var(value)), var(mapped_value)),
                    forall_where(
                        count,
                        is_list(var(count)),
                        computes_to(
                            map_call(var(function), replicate_call(var(count), var(value))),
                            replicate_call(var(count), var(mapped_value)),
                        ),
                    ),
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
pub fn zip_left_nil_theorem(right: Symbol) -> Prop {
    forall_where(
        right,
        is_list(var(right)),
        computes_to(zip_call(nil(), var(right)), nil()),
    )
}

/// Zipping with an empty right list returns `nil`.
pub fn zip_right_nil_theorem(left: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        computes_to(zip_call(var(left), nil()), nil()),
    )
}

/// Zipping two conses pairs the heads and recurs on the tails.
pub fn zip_cons_theorem(
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
                        zip_call(
                            cons(var(left_head), var(left_tail)),
                            cons(var(right_head), var(right_tail)),
                        ),
                        cons(
                            pair(var(left_head), var(right_head)),
                            zip_call(var(left_tail), var(right_tail)),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Zipping two lists returns a list of two-element-list pairs.
pub fn zip_computes_to_list_theorem(left: Symbol, right: Symbol, result: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        forall_where(
            right,
            is_list(var(right)),
            computes_to_list(result, zip_call(var(left), var(right))),
        ),
    )
}

/// `zip` produces a list whose elements are encoded pairs.
pub fn zip_pair_shape_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_list(var(left)),
        forall_where(
            right,
            is_list(var(right)),
            computes_to(
                all_call(is_pair(), zip_call(var(left), var(right))),
                true_value(),
            ),
        ),
    )
}

/// Unzipping an empty list returns a pair of empty lists.
pub fn unzip_nil_theorem() -> Prop {
    computes_to(unzip_call(nil()), pair(nil(), nil()))
}

/// Unzipping a cons whose head is a two-element-list pair splits that pair and
/// recurs on the tail.
pub fn unzip_cons_theorem(left: Symbol, right: Symbol, tail: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            right,
            is_value(var(right)),
            forall_where(
                tail,
                is_list(var(tail)),
                computes_to(
                    unzip_call(cons(pair(var(left), var(right)), var(tail))),
                    pair(
                        cons(var(left), head_call(unzip_call(var(tail)))),
                        cons(var(right), head_call(tail_call(unzip_call(var(tail))))),
                    ),
                ),
            ),
        ),
    )
}

/// A list whose elements are all encoded pairs unzips to a pair of lists.
pub fn unzip_pair_shape_theorem(pairs: Symbol, left: Symbol, right: Symbol) -> Prop {
    forall_where(
        pairs,
        is_list(var(pairs)),
        implies(
            computes_to(all_call(is_pair(), var(pairs)), true_value()),
            exists_where(
                left,
                is_list(var(left)),
                exists_where(
                    right,
                    is_list(var(right)),
                    computes_to(unzip_call(var(pairs)), pair(var(left), var(right))),
                ),
            ),
        ),
    )
}

/// Zipping the two outputs of `unzip` reconstructs a list of encoded pairs.
pub fn zip_unzip_theorem(pairs: Symbol) -> Prop {
    forall_where(
        pairs,
        is_list(var(pairs)),
        implies(
            computes_to(all_call(is_pair(), var(pairs)), true_value()),
            computes_to(
                zip_call(
                    head_call(unzip_call(var(pairs))),
                    head_call(tail_call(unzip_call(var(pairs)))),
                ),
                var(pairs),
            ),
        ),
    )
}

pub fn zip_pair_map_function(function: Computation, pair_value: Symbol) -> Computation {
    lambda(
        pair_value,
        apply(
            apply(function, head_call(var(pair_value))),
            head_call(tail_call(var(pair_value))),
        ),
    )
}

/// `zip-with f xs ys` is mapping the pair eliminator for `f` over `zip xs ys`.
pub fn zip_with_as_map_zip_theorem(
    function: Symbol,
    left: Symbol,
    right: Symbol,
    pair_value: Symbol,
) -> Prop {
    let mapped_pair = zip_pair_map_function(var(function), pair_value);
    forall_where(
        function,
        is_value(var(function)),
        forall_where(
            left,
            is_list(var(left)),
            forall_where(
                right,
                is_list(var(right)),
                computes_to(
                    zip_with_call(var(function), var(left), var(right)),
                    map_call(mapped_pair, zip_call(var(left), var(right))),
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

/// Partitioning `nil` returns a pair of empty lists.
pub fn partition_nil_theorem(predicate: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        computes_to(partition_call(var(predicate), nil()), pair(nil(), nil())),
    )
}

/// If the predicate returns true for the head, partition puts the head in the
/// first returned list.
pub fn partition_cons_true_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
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
                        partition_call(var(predicate), cons(var(head), var(tail))),
                        pair(
                            cons(
                                var(head),
                                head_call(partition_call(var(predicate), var(tail))),
                            ),
                            head_call(tail_call(partition_call(var(predicate), var(tail)))),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// If the predicate returns false for the head, partition puts the head in the
/// second returned list.
pub fn partition_cons_false_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
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
                        partition_call(var(predicate), cons(var(head), var(tail))),
                        pair(
                            head_call(partition_call(var(predicate), var(tail))),
                            cons(
                                var(head),
                                head_call(tail_call(partition_call(var(predicate), var(tail)))),
                            ),
                        ),
                    ),
                ),
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

/// A computation whose symbol-kind test returns true has a false list-kind test.
pub fn is_symbol_true_implies_is_list_value_false_theorem(value: Symbol) -> Prop {
    forall(
        value,
        implies(
            computes_to(is_symbol_call(var(value)), true_value()),
            computes_to(is_list_value_call(var(value)), false_value()),
        ),
    )
}

/// A computation whose lambda-kind test returns true has a false symbol-kind test.
pub fn is_lambda_true_implies_is_symbol_false_theorem(value: Symbol) -> Prop {
    forall(
        value,
        implies(
            computes_to(is_lambda_call(var(value)), true_value()),
            computes_to(is_symbol_call(var(value)), false_value()),
        ),
    )
}

/// A computation whose lambda-kind test returns true has a false list-kind test.
pub fn is_lambda_true_implies_is_list_value_false_theorem(value: Symbol) -> Prop {
    forall(
        value,
        implies(
            computes_to(is_lambda_call(var(value)), true_value()),
            computes_to(is_list_value_call(var(value)), false_value()),
        ),
    )
}

/// A computation whose list-kind test returns true has a false symbol-kind test.
pub fn is_list_value_true_implies_is_symbol_false_theorem(value: Symbol) -> Prop {
    forall(
        value,
        implies(
            computes_to(is_list_value_call(var(value)), true_value()),
            computes_to(is_symbol_call(var(value)), false_value()),
        ),
    )
}

/// A computation whose list-kind test returns true has a false lambda-kind test.
pub fn is_list_value_true_implies_is_lambda_false_theorem(value: Symbol) -> Prop {
    forall(
        value,
        implies(
            computes_to(is_list_value_call(var(value)), true_value()),
            computes_to(is_lambda_call(var(value)), false_value()),
        ),
    )
}

/// A finalized value has exactly one value kind.
pub fn value_kind_exactly_one_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        or(
            and(
                computes_to(is_symbol_call(var(value)), true_value()),
                and(
                    computes_to(is_lambda_call(var(value)), false_value()),
                    computes_to(is_list_value_call(var(value)), false_value()),
                ),
            ),
            or(
                and(
                    computes_to(is_lambda_call(var(value)), true_value()),
                    and(
                        computes_to(is_symbol_call(var(value)), false_value()),
                        computes_to(is_list_value_call(var(value)), false_value()),
                    ),
                ),
                and(
                    computes_to(is_list_value_call(var(value)), true_value()),
                    and(
                        computes_to(is_symbol_call(var(value)), false_value()),
                        computes_to(is_lambda_call(var(value)), false_value()),
                    ),
                ),
            ),
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

/// Comparable values contain no lambdas at the top level.
pub fn value_eq_comparable_no_lambdas_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        implies(
            computes_to(value_eq_comparable_call(var(value)), true_value()),
            computes_to(is_lambda_call(var(value)), false_value()),
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

/// If cons `value-eq` returns false, either the heads or tails return false under `value-eq`.
pub fn value_eq_cons_false_cases_theorem(
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
                            false_value(),
                        ),
                        or(
                            computes_to(
                                value_eq_call(var(left_head), var(right_head)),
                                false_value(),
                            ),
                            computes_to(
                                value_eq_call(var(left_tail), var(right_tail)),
                                false_value(),
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

/// `value-eq` is transitive when it returns true.
pub fn value_eq_trans_theorem(left: Symbol, middle: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            middle,
            is_value(var(middle)),
            forall_where(
                right,
                is_value(var(right)),
                implies(
                    computes_to(value_eq_call(var(left), var(middle)), true_value()),
                    implies(
                        computes_to(value_eq_call(var(middle), var(right)), true_value()),
                        computes_to(value_eq_call(var(left), var(right)), true_value()),
                    ),
                ),
            ),
        ),
    )
}

/// Kernel-equal comparable values are equal according to `value-eq`.
pub fn value_eq_complete_for_comparable_values_theorem(left: Symbol, right: Symbol) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            right,
            is_value(var(right)),
            implies(
                computes_to(value_eq_comparable_call(var(left)), true_value()),
                implies(
                    computes_to(value_eq_comparable_call(var(right)), true_value()),
                    implies(
                        computes_to(var(left), var(right)),
                        computes_to(value_eq_call(var(left), var(right)), true_value()),
                    ),
                ),
            ),
        ),
    )
}

/// A false `value-eq` result contradicts kernel equality for comparable values.
pub fn value_eq_false_implies_not_equal_for_comparable_values_theorem(
    left: Symbol,
    right: Symbol,
) -> Prop {
    forall_where(
        left,
        is_value(var(left)),
        forall_where(
            right,
            is_value(var(right)),
            implies(
                computes_to(value_eq_comparable_call(var(left)), true_value()),
                implies(
                    computes_to(value_eq_comparable_call(var(right)), true_value()),
                    implies(
                        computes_to(value_eq_call(var(left), var(right)), false_value()),
                        implies(computes_to(var(left), var(right)), absurd()),
                    ),
                ),
            ),
        ),
    )
}

/// A symbol value cannot compute to a list value.
pub fn symbol_not_list_theorem(symbol_value: Symbol, list_value: Symbol) -> Prop {
    forall_where(
        symbol_value,
        is_value(var(symbol_value)),
        implies(
            computes_to(is_symbol_call(var(symbol_value)), true_value()),
            forall_where(
                list_value,
                is_list(var(list_value)),
                implies(computes_to(var(symbol_value), var(list_value)), absurd()),
            ),
        ),
    )
}

/// A symbol value cannot compute to a lambda value.
pub fn symbol_not_lambda_theorem(symbol_value: Symbol, lambda_value: Symbol) -> Prop {
    forall_where(
        symbol_value,
        is_value(var(symbol_value)),
        implies(
            computes_to(is_symbol_call(var(symbol_value)), true_value()),
            forall_where(
                lambda_value,
                is_value(var(lambda_value)),
                implies(
                    computes_to(is_lambda_call(var(lambda_value)), true_value()),
                    implies(computes_to(var(symbol_value), var(lambda_value)), absurd()),
                ),
            ),
        ),
    )
}

/// A list value cannot compute to a lambda value.
pub fn list_not_lambda_theorem(list_value: Symbol, lambda_value: Symbol) -> Prop {
    forall_where(
        list_value,
        is_list(var(list_value)),
        forall_where(
            lambda_value,
            is_value(var(lambda_value)),
            implies(
                computes_to(is_lambda_call(var(lambda_value)), true_value()),
                implies(computes_to(var(list_value), var(lambda_value)), absurd()),
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

/// If `member` computes to a value, that value is boolean.
pub fn member_computes_to_bool_theorem(value: Symbol, list: Symbol, result: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        forall_where(
            list,
            is_list(var(list)),
            forall_where(
                result,
                is_value(var(result)),
                implies(
                    computes_to(member_call(var(value), var(list)), var(result)),
                    is_bool(var(result)),
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

/// `find` over `nil` returns `none`.
pub fn find_nil_theorem(predicate: Symbol) -> Prop {
    forall_where(
        predicate,
        is_value(var(predicate)),
        computes_to(find_call(var(predicate), nil()), none()),
    )
}

/// If the predicate returns true for the head, `find` returns that head.
pub fn find_cons_true_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
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
                        find_call(var(predicate), cons(var(head), var(tail))),
                        some_call(var(head)),
                    ),
                ),
            ),
        ),
    )
}

/// If the predicate returns false for the head, `find` recurs on the tail.
pub fn find_cons_false_theorem(predicate: Symbol, head: Symbol, tail: Symbol) -> Prop {
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
                        find_call(var(predicate), cons(var(head), var(tail))),
                        find_call(var(predicate), var(tail)),
                    ),
                ),
            ),
        ),
    )
}

/// Finding over an append searches the right side only if the left side has no match.
pub fn find_append_theorem(predicate: Symbol, value: Symbol, left: Symbol, right: Symbol) -> Prop {
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
                left,
                is_list(var(left)),
                forall_where(
                    right,
                    is_list(var(right)),
                    computes_to(
                        find_call(var(predicate), append_call(var(left), var(right))),
                        if_call(
                            any_call(var(predicate), var(left)),
                            find_call(var(predicate), var(left)),
                            find_call(var(predicate), var(right)),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Searching `nil` for an element returns `none`.
pub fn elem_index_nil_theorem(value: Symbol) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        computes_to(elem_index_call(var(value), nil()), none()),
    )
}

/// If the head equals the searched value, `elem-index` returns zero.
pub fn elem_index_cons_true_theorem(value: Symbol, head: Symbol, tail: Symbol) -> Prop {
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
                        elem_index_call(var(value), cons(var(head), var(tail))),
                        some_call(nil()),
                    ),
                ),
            ),
        ),
    )
}

/// If the head misses and the tail misses, `elem-index` returns `none`.
pub fn elem_index_cons_false_none_theorem(value: Symbol, head: Symbol, tail: Symbol) -> Prop {
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
                    implies(
                        computes_to(elem_index_call(var(value), var(tail)), none()),
                        computes_to(
                            elem_index_call(var(value), cons(var(head), var(tail))),
                            none(),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// If the head misses and the tail finds index `i`, `elem-index` returns
/// `succ i`.
pub fn elem_index_cons_false_some_theorem(
    value: Symbol,
    head: Symbol,
    tail: Symbol,
    index: Symbol,
) -> Prop {
    forall_where(
        value,
        is_value(var(value)),
        forall_where(
            head,
            is_value(var(head)),
            forall_where(
                tail,
                is_list(var(tail)),
                forall_where(
                    index,
                    is_list(var(index)),
                    implies(
                        computes_to(value_eq_call(var(value), var(head)), false_value()),
                        implies(
                            computes_to(
                                elem_index_call(var(value), var(tail)),
                                some_call(var(index)),
                            ),
                            computes_to(
                                elem_index_call(var(value), cons(var(head), var(tail))),
                                some_call(cons(unit(), var(index))),
                            ),
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

pub fn fold_right_map_function(
    fold_function: Computation,
    map_function: Computation,
    value: Symbol,
    accumulator: Symbol,
) -> Computation {
    lambda(
        value,
        lambda(
            accumulator,
            apply(
                apply(fold_function, apply(map_function, var(value))),
                var(accumulator),
            ),
        ),
    )
}

pub fn fold_left_map_function(
    fold_function: Computation,
    map_function: Computation,
    accumulator: Symbol,
    value: Symbol,
) -> Computation {
    lambda(
        accumulator,
        lambda(
            value,
            apply(
                apply(fold_function, var(accumulator)),
                apply(map_function, var(value)),
            ),
        ),
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

/// Mapping over the option returned by `nth` agrees with taking `nth` after `map`.
pub fn option_map_nth_theorem(
    function: Symbol,
    value: Symbol,
    mapped_value: Symbol,
    index: Symbol,
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
                index,
                is_list(var(index)),
                forall_where(
                    list,
                    is_list(var(list)),
                    computes_to(
                        option_map_call(var(function), nth_call(var(index), var(list))),
                        nth_call(var(index), map_call(var(function), var(list))),
                    ),
                ),
            ),
        ),
    )
}

/// Mapping over a snoc maps the appended value and snocs it onto the mapped list.
pub fn map_snoc_theorem(
    function: Symbol,
    input_value: Symbol,
    mapped_value: Symbol,
    list: Symbol,
    snoc_value: Symbol,
) -> Prop {
    forall_where(
        function,
        is_value(var(function)),
        implies(
            forall_where(
                input_value,
                is_value(var(input_value)),
                exists_where(
                    mapped_value,
                    is_value(var(mapped_value)),
                    computes_to(apply(var(function), var(input_value)), var(mapped_value)),
                ),
            ),
            forall_where(
                list,
                is_list(var(list)),
                forall_where(
                    snoc_value,
                    is_value(var(snoc_value)),
                    computes_to(
                        map_call(var(function), snoc_call(var(list), var(snoc_value))),
                        snoc_call(
                            map_call(var(function), var(list)),
                            apply(var(function), var(snoc_value)),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// `concat-map` agrees with concatenating a mapped list when the function returns lists.
pub fn concat_map_as_concat_map_theorem(
    function: Symbol,
    value: Symbol,
    mapped_list: Symbol,
    list: Symbol,
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
                computes_to(
                    concat_map_call(var(function), var(list)),
                    concat_call(map_call(var(function), var(list))),
                ),
            ),
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

/// Folding right over an append folds the right side into the initial accumulator first.
pub fn fold_right_append_theorem(
    function: Symbol,
    initial: Symbol,
    value: Symbol,
    accumulator: Symbol,
    folded_value: Symbol,
    left: Symbol,
    right: Symbol,
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
                    left,
                    is_list(var(left)),
                    forall_where(
                        right,
                        is_list(var(right)),
                        computes_to(
                            fold_right_call(
                                var(function),
                                var(initial),
                                append_call(var(left), var(right)),
                            ),
                            fold_right_call(
                                var(function),
                                fold_right_call(var(function), var(initial), var(right)),
                                var(left),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Folding left over an append uses the left fold as the right side's initial accumulator.
pub fn fold_left_append_theorem(
    function: Symbol,
    accumulator: Symbol,
    value: Symbol,
    folded_value: Symbol,
    left: Symbol,
    initial: Symbol,
    right: Symbol,
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
                left,
                is_list(var(left)),
                forall_where(
                    initial,
                    is_value(var(initial)),
                    forall_where(
                        right,
                        is_list(var(right)),
                        computes_to(
                            fold_left_call(
                                var(function),
                                var(initial),
                                append_call(var(left), var(right)),
                            ),
                            fold_left_call(
                                var(function),
                                fold_left_call(var(function), var(initial), var(left)),
                                var(right),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Folding right after mapping is folding right with a composed combining function.
pub fn fold_right_map_theorem(
    fold_function: Symbol,
    map_function: Symbol,
    initial: Symbol,
    value: Symbol,
    mapped_value: Symbol,
    fold_value: Symbol,
    accumulator: Symbol,
    folded_value: Symbol,
    list: Symbol,
    composed_value: Symbol,
    composed_accumulator: Symbol,
) -> Prop {
    let composed = fold_right_map_function(
        var(fold_function),
        var(map_function),
        composed_value,
        composed_accumulator,
    );

    forall_where(
        fold_function,
        is_value(var(fold_function)),
        forall_where(
            map_function,
            is_value(var(map_function)),
            forall_where(
                initial,
                is_value(var(initial)),
                implies(
                    forall_where(
                        value,
                        is_value(var(value)),
                        exists_where(
                            mapped_value,
                            is_value(var(mapped_value)),
                            computes_to(apply(var(map_function), var(value)), var(mapped_value)),
                        ),
                    ),
                    implies(
                        forall_where(
                            fold_value,
                            is_value(var(fold_value)),
                            forall_where(
                                accumulator,
                                is_value(var(accumulator)),
                                exists_where(
                                    folded_value,
                                    is_value(var(folded_value)),
                                    computes_to(
                                        apply(
                                            apply(var(fold_function), var(fold_value)),
                                            var(accumulator),
                                        ),
                                        var(folded_value),
                                    ),
                                ),
                            ),
                        ),
                        forall_where(
                            list,
                            is_list(var(list)),
                            computes_to(
                                fold_right_call(
                                    var(fold_function),
                                    var(initial),
                                    map_call(var(map_function), var(list)),
                                ),
                                fold_right_call(composed, var(initial), var(list)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Folding left after mapping is folding left with a composed combining function.
pub fn fold_left_map_theorem(
    fold_function: Symbol,
    map_function: Symbol,
    value: Symbol,
    mapped_value: Symbol,
    accumulator: Symbol,
    fold_value: Symbol,
    folded_value: Symbol,
    list: Symbol,
    initial: Symbol,
    composed_accumulator: Symbol,
    composed_value: Symbol,
) -> Prop {
    let composed = fold_left_map_function(
        var(fold_function),
        var(map_function),
        composed_accumulator,
        composed_value,
    );

    forall_where(
        fold_function,
        is_value(var(fold_function)),
        forall_where(
            map_function,
            is_value(var(map_function)),
            implies(
                forall_where(
                    value,
                    is_value(var(value)),
                    exists_where(
                        mapped_value,
                        is_value(var(mapped_value)),
                        computes_to(apply(var(map_function), var(value)), var(mapped_value)),
                    ),
                ),
                implies(
                    forall_where(
                        accumulator,
                        is_value(var(accumulator)),
                        forall_where(
                            fold_value,
                            is_value(var(fold_value)),
                            exists_where(
                                folded_value,
                                is_value(var(folded_value)),
                                computes_to(
                                    apply(
                                        apply(var(fold_function), var(accumulator)),
                                        var(fold_value),
                                    ),
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
                            computes_to(
                                fold_left_call(
                                    var(fold_function),
                                    var(initial),
                                    map_call(var(map_function), var(list)),
                                ),
                                fold_left_call(composed, var(initial), var(list)),
                            ),
                        ),
                    ),
                ),
            ),
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
    const COUNT: Symbol = Symbol(220);
    const COUNT_HEAD: Symbol = Symbol(221);
    const COUNT_TAIL: Symbol = Symbol(222);
    const COUNT_VALUE: Symbol = Symbol(223);
    const LIST_VALUE: Symbol = Symbol(224);
    const LEFT_LIST: Symbol = Symbol(225);

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
