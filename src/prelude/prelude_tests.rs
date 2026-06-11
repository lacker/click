//! Prelude loader tests.

use super::*;
use crate::{
    Computation, ComputationDefinitionError, LAMBDA_KIND_SYMBOL, LIST_KIND_SYMBOL, Proof,
    SYMBOL_KIND_SYMBOL, Step, Theorem, TheoremError, computes_to_list, elab::proof, is_list,
};

fn computation(spelling: &str) -> Name {
    computation_name(spelling).expect("prelude should define requested computation")
}

fn theorem(spelling: &str) -> Name {
    theorem_name(spelling).expect("prelude should define requested theorem")
}

fn symbol(spelling: &str) -> Symbol {
    symbol_name(spelling).expect("prelude should define requested symbol")
}

fn computation_ref(spelling: &str) -> Computation {
    Computation::Ref(computation(spelling))
}

fn checked_theorem(spelling: &str) -> Option<Theorem> {
    theory().known(theorem(spelling))
}

fn reverse_acc() -> Computation {
    computation_ref("reverse_acc")
}

fn reverse() -> Computation {
    computation_ref("reverse")
}

fn append() -> Computation {
    computation_ref("append")
}

fn snoc() -> Computation {
    computation_ref("snoc")
}

fn concat() -> Computation {
    computation_ref("concat")
}

fn length() -> Computation {
    computation_ref("length")
}

fn take() -> Computation {
    computation_ref("take")
}

fn drop() -> Computation {
    computation_ref("drop")
}

fn split_at() -> Computation {
    computation_ref("split-at")
}

fn nth() -> Computation {
    computation_ref("nth")
}

fn replicate() -> Computation {
    computation_ref("replicate")
}

fn intersperse() -> Computation {
    computation_ref("intersperse")
}

fn intercalate() -> Computation {
    computation_ref("intercalate")
}

fn map() -> Computation {
    computation_ref("map")
}

fn concat_map() -> Computation {
    computation_ref("concat-map")
}

fn fold_right() -> Computation {
    computation_ref("fold-right")
}

fn fold_left() -> Computation {
    computation_ref("fold-left")
}

fn zip() -> Computation {
    computation_ref("zip")
}

fn unzip() -> Computation {
    computation_ref("unzip")
}

fn zip_with() -> Computation {
    computation_ref("zip-with")
}

fn filter() -> Computation {
    computation_ref("filter")
}

fn partition() -> Computation {
    computation_ref("partition")
}

fn any() -> Computation {
    computation_ref("any")
}

fn all() -> Computation {
    computation_ref("all")
}

fn find() -> Computation {
    computation_ref("find")
}

fn bool_not() -> Computation {
    computation_ref("not")
}

fn bool_and() -> Computation {
    computation_ref("and")
}

fn bool_or() -> Computation {
    computation_ref("or")
}

fn all_lists() -> Computation {
    computation_ref("all-lists")
}

fn none() -> Computation {
    computation_ref("none")
}

fn some() -> Computation {
    computation_ref("some")
}

fn is_none() -> Computation {
    computation_ref("is-none")
}

fn is_some() -> Computation {
    computation_ref("is-some")
}

fn option_map() -> Computation {
    computation_ref("option-map")
}

fn option_bind() -> Computation {
    computation_ref("option-bind")
}

fn unwrap_or() -> Computation {
    computation_ref("unwrap-or")
}

fn option_filter() -> Computation {
    computation_ref("option-filter")
}

fn is_symbol() -> Computation {
    computation_ref("is-symbol")
}

fn is_lambda() -> Computation {
    computation_ref("is-lambda")
}

fn is_list_value() -> Computation {
    computation_ref("is-list-value")
}

fn value_eq() -> Computation {
    computation_ref("value-eq")
}

fn value_eq_comparable() -> Computation {
    computation_ref("value-eq-comparable")
}

fn member() -> Computation {
    computation_ref("member")
}

fn elem_index() -> Computation {
    computation_ref("elem-index")
}

fn last() -> Computation {
    computation_ref("last")
}

fn init() -> Computation {
    computation_ref("init")
}

fn null() -> Computation {
    computation_ref("null")
}

fn is_singleton() -> Computation {
    computation_ref("is-singleton")
}

fn is_pair() -> Computation {
    computation_ref("is-pair")
}

fn zero() -> Computation {
    computation_ref("zero")
}

fn succ() -> Computation {
    computation_ref("succ")
}

fn is_nat_value() -> Computation {
    computation_ref("is-nat-value")
}

fn is_zero() -> Computation {
    computation_ref("is-zero")
}

fn pred() -> Computation {
    computation_ref("pred")
}

fn range() -> Computation {
    computation_ref("range")
}

fn add() -> Computation {
    computation_ref("add")
}

fn mul() -> Computation {
    computation_ref("mul")
}

fn parse_test_module(source: &str) -> (source::ParsedModule, SourceEnv) {
    let mut env = prelude_source_env();
    let module = env
        .parse_module(source)
        .expect("synthetic module should parse");
    (module, env)
}

fn prelude_theorem_names() -> Vec<Name> {
    [
        "nil_is_list",
        "cons_is_list",
        "cons_head",
        "cons_tail",
        "nil_not_cons",
        "cons_not_nil",
        "cons_injective_head",
        "cons_injective_tail",
        "cons_injective",
        "list_eta",
        "reverse_acc_computes_to_list",
        "reverse_computes_to_list",
        "reverse_nil_computes_to_list",
        "reverse_nil",
        "reverse_singleton",
        "reverse_congr",
        "append_nil_computes_to_list",
        "append_computes_to_list",
        "append_nil_returns_right",
        "append_right_nil",
        "append_cons",
        "append_singleton",
        "append_congr_left",
        "append_congr_right",
        "append_congr",
        "append_assoc",
        "reverse_acc_append",
        "reverse_cons",
        "reverse_acc_reverse",
        "reverse_double",
        "reverse_acc_of_append",
        "reverse_append",
        "map_reverse",
        "snoc_computes_to_list",
        "snoc_nil",
        "snoc_cons",
        "member_snoc",
        "tail_snoc_after_snoc",
        "all_lists_snoc",
        "concat_nil",
        "concat_cons",
        "concat_computes_to_list",
        "concat_append",
        "map_length_nil",
        "map_length_cons",
        "map_length_computes_to_list",
        "length_concat",
        "length_nil",
        "length_cons",
        "length_singleton",
        "length_computes_to_list",
        "length_append",
        "append_length_singleton",
        "length_snoc",
        "length_take",
        "length_drop",
        "length_take_add_length_drop",
        "length_reverse",
        "take_zero",
        "take_nil",
        "take_cons",
        "take_computes_to_list",
        "take_congr_count_computation",
        "take_congr_list_computation",
        "drop_zero",
        "drop_nil",
        "drop_cons",
        "drop_computes_to_list",
        "drop_congr_count_computation",
        "drop_congr_list_computation",
        "take_take",
        "split_at_def",
        "split_at_zero",
        "split_at_nil",
        "split_at_cons",
        "split_at_computes_to_pair",
        "split_at_first_take",
        "split_at_second_drop",
        "nth_zero_nil",
        "nth_zero_cons",
        "nth_cons_nil",
        "nth_cons_cons",
        "nth_zero_cons_some",
        "nth_out_of_bounds_none",
        "nth_computes_to_option",
        "take_length",
        "drop_length",
        "nth_zero_after_drop",
        "nth_after_split_at",
        "replicate_zero",
        "replicate_cons",
        "replicate_computes_to_list",
        "length_replicate",
        "take_replicate",
        "drop_replicate",
        "intersperse_nil",
        "intersperse_singleton",
        "intersperse_cons_cons",
        "intersperse_cons_computes_to_list",
        "intersperse_computes_to_list",
        "intercalate_nil",
        "intercalate_singleton",
        "intercalate_cons_cons",
        "is_list_value_true_implies_is_list",
        "value_kind_list_implies_is_list",
        "is_list_implies_is_list_value_true",
        "all_lists_cons",
        "all_lists_cons_true",
        "none_is_none",
        "some_is_none",
        "none_is_some",
        "some_is_some",
        "some_tag_from_computation",
        "some_value_from_computation",
        "some_none_absurd",
        "none_some_absurd",
        "some_congr",
        "some_injective",
        "option_map_none",
        "option_map_some",
        "option_bind_none",
        "option_bind_some",
        "unwrap_or_none",
        "unwrap_or_some",
        "option_filter_none",
        "option_filter_some_true",
        "option_filter_some_false",
        "option_map_computes_to_option",
        "option_bind_computes_to_option",
        "unwrap_or_computes_to_value",
        "option_filter_computes_to_option",
        "option_map_identity",
        "option_map_compose",
        "option_bind_left_identity",
        "option_bind_right_identity",
        "option_bind_assoc",
        "option_map_congr_function",
        "option_map_congr_option",
        "option_map_congr_option_computation",
        "option_map_congr",
        "option_bind_congr_function",
        "option_bind_congr_option",
        "option_bind_congr_option_computation",
        "unwrap_or_congr_default",
        "unwrap_or_congr_option",
        "pair_first",
        "pair_tail",
        "pair_second",
        "pair_computes_to_list",
        "pair_computes_to_value",
        "pair_eta",
        "pair_congr",
        "pair_first_from_computation",
        "pair_second_from_computation",
        "pair_injective_first",
        "pair_injective_second",
        "pair_injective",
        "list_pair_first_from_computation",
        "list_pair_second_from_computation",
        "intercalate_cons_computes_to_list",
        "intercalate_computes_to_list",
        "map_nil",
        "map_cons",
        "map_computes_to_list",
        "length_map",
        "map_replicate",
        "concat_map_nil",
        "concat_map_cons",
        "concat_map_computes_to_list",
        "fold_right_nil",
        "fold_right_cons",
        "fold_right_computes_to_value",
        "fold_right_congr",
        "fold_left_nil",
        "fold_left_cons",
        "fold_left_computes_to_value",
        "fold_left_congr",
        "zip_left_nil",
        "zip_right_nil",
        "zip_cons",
        "zip_computes_to_list",
        "zip_pair_shape",
        "unzip_nil",
        "unzip_cons",
        "unzip_pair_shape",
        "zip_unzip",
        "unzip_zip",
        "zip_with_as_map_zip",
        "zip_with_left_nil",
        "zip_with_right_nil",
        "zip_with_cons",
        "zip_with_computes_to_list",
        "filter_nil",
        "filter_cons_true",
        "filter_cons_false",
        "reject_nil",
        "reject_cons_true",
        "reject_cons_false",
        "filter_computes_to_list",
        "filter_congr",
        "reject_computes_to_list",
        "filter_append",
        "reject_append",
        "filter_idempotent",
        "reject_idempotent",
        "partition_nil",
        "partition_cons_true",
        "partition_cons_false",
        "partition_computes_to_pair",
        "partition_first_filter",
        "partition_second_filter_false",
        "partition_second_reject",
        "partition_append_filter_reject",
        "partition_all_true",
        "partition_all_false",
        "any_nil",
        "any_cons_true",
        "any_cons_false",
        "any_cons_or",
        "any_computes_to_bool",
        "any_append",
        "any_cons_false_parts",
        "any_cons_true_cases",
        "all_true_implies_not_any_false",
        "any_true_implies_not_all_false",
        "find_nil",
        "find_cons_true",
        "find_cons_false",
        "find_append",
        "find_cons_branch",
        "find_cons_none_parts",
        "find_cons_some_cases",
        "find_computes_to_option",
        "any_false_implies_find_none",
        "any_true_implies_find_some",
        "find_none_implies_any_false",
        "find_some_implies_any_true",
        "value_eq_true_true",
        "value_eq_true_false",
        "value_eq_nil",
        "value_eq_nil_cons",
        "value_eq_cons_nil",
        "value_eq_cons",
        "value_kind_symbol_implies_is_symbol",
        "value_kind_lambda_implies_is_lambda",
        "is_symbol_true_implies_is_lambda_false",
        "is_symbol_true_implies_is_list_value_false",
        "is_lambda_true_implies_is_symbol_false",
        "is_lambda_true_implies_is_list_value_false",
        "is_list_value_true_implies_is_symbol_false",
        "is_list_value_true_implies_is_lambda_false",
        "value_kind_exactly_one",
        "value_eq_comparable_symbol",
        "value_eq_comparable_nil",
        "value_eq_comparable_cons",
        "value_eq_comparable_no_lambdas",
        "value_eq_true_implies_not_lambdas",
        "value_non_symbol_non_lambda_non_bv32_is_list",
        "value_eq_left_non_symbol_true_implies_lists",
        "value_eq_left_symbol_true",
        "value_eq_left_symbol_sound",
        "value_eq_cons_true_elim",
        "value_eq_cons_false_cases",
        "cons_congr",
        "value_eq_sound",
        "value_eq_refl",
        "value_eq_true_implies_comparable_left",
        "value_eq_true_implies_comparable_right",
        "value_eq_symm",
        "value_eq_trans",
        "value_eq_complete_for_comparable_values",
        "value_eq_false_implies_not_equal_for_comparable_values",
        "symbol_not_list",
        "symbol_not_lambda",
        "list_not_lambda",
        "member_nil",
        "member_cons_true",
        "member_cons_false",
        "member_computes_to_bool",
        "member_is_bool_for_comparable_value",
        "member_cons_or",
        "member_append",
        "elem_index_computes_to_option",
        "member_false_implies_elem_index_none",
        "member_true_implies_elem_index_some",
        "elem_index_none_implies_member_false",
        "elem_index_some_implies_member_true",
        "elem_index_cons_some_cases",
        "elem_index_append_left",
        "elem_index_cons_none_parts",
        "elem_index_append_right",
        "all_nil",
        "all_cons_true",
        "all_cons_false",
        "all_cons_and",
        "all_computes_to_bool",
        "all_cons_true_parts",
        "all_append",
        "map_identity",
        "map_compose",
        "map_congr",
        "map_append",
        "map_snoc",
        "map_take",
        "map_drop",
        "option_map_nth",
        "option_map_find",
        "option_bind_find_none",
        "option_bind_find_some",
        "concat_map_singleton",
        "concat_map_append",
        "concat_map_as_concat_map",
        "fold_right_cons_nil",
        "fold_right_append",
        "fold_left_append",
        "fold_right_map",
        "fold_left_map",
        "fold_left_reverse_acc",
        "fold_left_reverse",
        "append_take_drop",
        "drop_drop",
        "take_drop_commute",
        "split_at_append",
        "split_at_pair_eta",
        "last_nil_errors",
        "last_singleton",
        "last_cons",
        "init_nil_errors",
        "init_singleton",
        "init_cons",
        "null_nil",
        "null_cons",
        "is_singleton_nil",
        "is_singleton_singleton",
        "is_singleton_cons",
        "is_pair_nil_false",
        "is_pair_singleton_false",
        "is_pair_cons_cons_nil_true",
        "is_pair_cons_cons_cons_false",
        "is_pair_cons_cons_true_elim",
        "is_pair_cons_true_elim",
        "is_pair_true_elim",
        "all_is_pair_cons_true_parts",
        "if_true",
        "if_false",
        "if_condition_true",
        "if_condition_false",
        "if_true_result_with_false_else",
        "if_true_result_with_error_then",
        "if_true_result_with_false_then",
        "if_false_result_with_true_then",
        "if_false_result_with_true_else",
        "if_false_result_with_error_else",
        "if_false_result_with_false_else",
        "if_true_result_with_true_then",
        "if_true_result_with_true_else",
        "if_false_result_with_false_then",
        "symbol_eq_unit_unit",
        "symbol_eq_true_false",
        "symbol_eq_true",
        "symbol_eq_true_implies_is_symbol_left",
        "symbol_eq_true_implies_is_symbol_right",
        "symbol_eq_false_distinct",
        "symbol_eq_symm",
        "symbol_eq_refl",
        "symbol_eq_computes_to_bool",
        "true_is_bool",
        "false_is_bool",
        "is_bool_elim",
        "bool_distinct",
        "not_true",
        "not_false",
        "not_computes_to_bool",
        "not_congr",
        "and_congr_left",
        "and_congr_right",
        "and_congr",
        "or_congr_left",
        "or_congr_right",
        "or_congr",
        "not_true_elim",
        "not_false_elim",
        "if_computes_to_bool",
        "if_same",
        "if_not",
        "if_congr_condition",
        "if_congr_then",
        "if_congr_else",
        "and_true_left",
        "and_false_left",
        "and_computes_to_bool",
        "and_true_intro",
        "and_true_elim_left",
        "and_true_elim_right",
        "and_false_cases",
        "or_true_left",
        "or_false_left",
        "or_computes_to_bool",
        "or_false_intro",
        "or_false_elim_left",
        "or_false_elim_right",
        "or_true_cases",
        "and_prop_to_bool",
        "and_bool_to_prop",
        "or_prop_to_bool_left",
        "or_prop_to_bool_right",
        "or_bool_to_prop",
        "not_bool_to_absurd",
        "not_absurd_to_bool_false",
        "not_not",
        "and_true_right",
        "and_false_right",
        "or_true_right",
        "or_false_right",
        "and_comm",
        "and_assoc",
        "and_idempotent",
        "or_comm",
        "or_assoc",
        "or_idempotent",
        "and_absorb_or",
        "or_absorb_and",
        "and_distrib_or_left",
        "and_distrib_or_right",
        "or_distrib_and_left",
        "or_distrib_and_right",
        "not_and",
        "not_or",
        "add_is_append",
        "zero_computes_to_list",
        "zero_is_nat_value",
        "succ_zero",
        "is_zero_zero",
        "is_zero_succ",
        "pred_zero",
        "pred_succ",
        "is_zero_pred_succ",
        "pred_computes_to_list",
        "succ_computes_to_list",
        "range_zero",
        "range_cons",
        "range_succ",
        "range_computes_to_list",
        "range_all_lists",
        "map_succ_computes_to_list",
        "map_succ_snoc",
        "map_succ_range",
        "length_range",
        "succ_preserves_nat_value",
        "is_nat_value_cons",
        "is_nat_value_cons_true_elim",
        "add_zero_left",
        "add_computes_to_list",
        "add_cons",
        "add_succ_left",
        "pred_add_succ_left",
        "is_zero_add_succ_left",
        "add_cons_unit_right",
        "add_succ_right",
        "pred_add_succ_right",
        "is_zero_add_succ_right",
        "add_zero_right",
        "add_nat_suffix_preserves_nat_value",
        "add_preserves_nat_value",
        "add_assoc",
        "add_comm",
        "add_swap",
        "mul_zero_left",
        "is_zero_mul_zero_left",
        "mul_cons",
        "mul_computes_to_list",
        "mul_preserves_nat_value",
        "mul_succ_left",
        "is_zero_mul_succ_succ",
        "pred_mul_succ_succ",
        "mul_succ_right",
        "mul_zero_right",
        "is_zero_mul_zero_right",
        "mul_one_left",
        "mul_one_right",
        "mul_comm",
        "mul_add_left_distrib",
        "mul_assoc",
        "mul_add_right_distrib",
    ]
    .into_iter()
    .map(theorem)
    .collect()
}

#[test]
fn loaded_prelude_exposes_theory_and_source_environment() {
    let loaded = loaded();
    let sections: Vec<_> = loaded
        .modules()
        .iter()
        .map(|module| module.section().map(SourceSection::name))
        .collect();

    assert_eq!(
        sections,
        vec![
            Some("list/core"),
            Some("list/booleans"),
            Some("list/operations"),
            Some("list/value_eq"),
            Some("list/derived"),
            Some("nat/core"),
            Some("nat/order"),
            Some("nat/add"),
            Some("nat/sub"),
            Some("nat/mul"),
        ]
    );

    assert_eq!(loaded.computation("append"), Some(computation("append")));
    assert_eq!(loaded.computation("take"), Some(computation("take")));
    assert_eq!(
        loaded.computation("replicate"),
        Some(computation("replicate"))
    );
    assert_eq!(
        loaded.computation("intersperse"),
        Some(computation("intersperse"))
    );
    assert_eq!(
        loaded.computation("intercalate"),
        Some(computation("intercalate"))
    );
    assert_eq!(loaded.computation("not"), Some(computation("not")));
    assert_eq!(loaded.computation("and"), Some(computation("and")));
    assert_eq!(loaded.computation("or"), Some(computation("or")));
    assert_eq!(
        loaded.computation("option-map"),
        Some(computation("option-map"))
    );
    assert_eq!(
        loaded.computation("option-bind"),
        Some(computation("option-bind"))
    );
    assert_eq!(
        loaded.computation("unwrap-or"),
        Some(computation("unwrap-or"))
    );
    assert_eq!(
        loaded.computation("option-filter"),
        Some(computation("option-filter"))
    );
    assert_eq!(loaded.computation("zero"), Some(computation("zero")));
    assert_eq!(
        loaded.theorem("append_assoc"),
        Some(theorem("append_assoc"))
    );
    assert_eq!(
        loaded.theorem("add_computes_to_list"),
        Some(theorem("add_computes_to_list"))
    );
    assert_eq!(
        loaded.theorem("not_computes_to_bool"),
        Some(theorem("not_computes_to_bool"))
    );
    assert_eq!(loaded.symbol(":true"), Some(symbol(":true")));
    assert_eq!(loaded.symbol(":false"), Some(symbol(":false")));
    assert_eq!(loaded.symbol(":symbol"), Some(SYMBOL_KIND_SYMBOL));
    assert_eq!(loaded.symbol(":lambda"), Some(LAMBDA_KIND_SYMBOL));
    assert_eq!(loaded.symbol(":list"), Some(LIST_KIND_SYMBOL));
    assert_eq!(loaded.computation("missing"), None);
    assert_eq!(loaded.theorem("missing"), None);
    assert_eq!(loaded.symbol("missing"), None);
    assert_eq!(
        loaded.theory().computation(computation("append")),
        Some(&list_tests::append_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("take")),
        Some(&list_tests::take_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("replicate")),
        Some(&list_tests::replicate_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("intersperse")),
        Some(&list_tests::intersperse_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("intercalate")),
        Some(&list_tests::intercalate_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("not")),
        Some(&list_tests::bool_not_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("and")),
        Some(&list_tests::bool_and_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("or")),
        Some(&list_tests::bool_or_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("option-map")),
        Some(&list_tests::option_map_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("option-bind")),
        Some(&list_tests::option_bind_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("unwrap-or")),
        Some(&list_tests::unwrap_or_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("option-filter")),
        Some(&list_tests::option_filter_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("zero")),
        Some(&nat_tests::zero_definition())
    );
    assert_eq!(
        loaded.theory().theorem(theorem("append_assoc")),
        Some(&list_tests::append_assoc_source_theorem())
    );
    assert_eq!(
        loaded.theory().theorem(theorem("add_computes_to_list")),
        Some(&nat_tests::add_computes_to_list_source_theorem())
    );
    assert_eq!(
        loaded.source_env().computation("reverse_acc"),
        Some(computation("reverse_acc"))
    );
    assert_eq!(
        loaded.source_env().computation("take"),
        Some(computation("take"))
    );
    assert_eq!(
        loaded.source_env().computation("replicate"),
        Some(computation("replicate"))
    );
    assert_eq!(
        loaded.source_env().computation("intersperse"),
        Some(computation("intersperse"))
    );
    assert_eq!(
        loaded.source_env().computation("intercalate"),
        Some(computation("intercalate"))
    );
    assert_eq!(
        loaded.source_env().computation("not"),
        Some(computation("not"))
    );
    assert_eq!(
        loaded.source_env().computation("and"),
        Some(computation("and"))
    );
    assert_eq!(
        loaded.source_env().computation("or"),
        Some(computation("or"))
    );
    assert_eq!(
        loaded.source_env().computation("option-map"),
        Some(computation("option-map"))
    );
    assert_eq!(
        loaded.source_env().computation("option-bind"),
        Some(computation("option-bind"))
    );
    assert_eq!(
        loaded.source_env().computation("unwrap-or"),
        Some(computation("unwrap-or"))
    );
    assert_eq!(
        loaded.source_env().computation("option-filter"),
        Some(computation("option-filter"))
    );

    assert_eq!(
        computation_name("is-singleton"),
        Some(computation("is-singleton"))
    );
    assert_eq!(computation_name("is-pair"), Some(computation("is-pair")));
    assert_eq!(
        theorem_name("reverse_double"),
        Some(theorem("reverse_double"))
    );
    assert_eq!(symbol_name(":true"), Some(symbol(":true")));
    assert_eq!(symbol_name(":symbol"), Some(SYMBOL_KIND_SYMBOL));
    assert_eq!(symbol_name(":lambda"), Some(LAMBDA_KIND_SYMBOL));
    assert_eq!(symbol_name(":list"), Some(LIST_KIND_SYMBOL));
    assert_eq!(computation_name("zero"), Some(computation("zero")));
    assert_eq!(
        theorem_name("add_computes_to_list"),
        Some(theorem("add_computes_to_list"))
    );
    assert_eq!(
        theorem_name("not_computes_to_bool"),
        Some(theorem("not_computes_to_bool"))
    );
}

#[test]
fn loaded_computation_prelude_keeps_source_env_without_defining_theorems() {
    let loaded = loaded_computations();

    assert_eq!(loaded.computation("reverse"), Some(computation("reverse")));
    assert_eq!(loaded.computation("take"), Some(computation("take")));
    assert_eq!(
        loaded.computation("replicate"),
        Some(computation("replicate"))
    );
    assert_eq!(
        loaded.computation("intersperse"),
        Some(computation("intersperse"))
    );
    assert_eq!(
        loaded.computation("intercalate"),
        Some(computation("intercalate"))
    );
    assert_eq!(loaded.computation("not"), Some(computation("not")));
    assert_eq!(loaded.computation("and"), Some(computation("and")));
    assert_eq!(loaded.computation("or"), Some(computation("or")));
    assert_eq!(
        loaded.computation("option-map"),
        Some(computation("option-map"))
    );
    assert_eq!(
        loaded.computation("option-bind"),
        Some(computation("option-bind"))
    );
    assert_eq!(
        loaded.computation("unwrap-or"),
        Some(computation("unwrap-or"))
    );
    assert_eq!(
        loaded.computation("option-filter"),
        Some(computation("option-filter"))
    );
    assert_eq!(loaded.computation("add"), Some(computation("add")));
    assert_eq!(
        loaded.theorem("append_assoc"),
        Some(theorem("append_assoc"))
    );
    assert_eq!(
        loaded.theorem("add_computes_to_list"),
        Some(theorem("add_computes_to_list"))
    );
    assert_eq!(
        loaded.theory().computation(computation("reverse")),
        Some(&list_tests::reverse_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("take")),
        Some(&list_tests::take_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("replicate")),
        Some(&list_tests::replicate_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("intersperse")),
        Some(&list_tests::intersperse_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("intercalate")),
        Some(&list_tests::intercalate_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("not")),
        Some(&list_tests::bool_not_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("and")),
        Some(&list_tests::bool_and_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("or")),
        Some(&list_tests::bool_or_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("option-map")),
        Some(&list_tests::option_map_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("option-bind")),
        Some(&list_tests::option_bind_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("unwrap-or")),
        Some(&list_tests::unwrap_or_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("option-filter")),
        Some(&list_tests::option_filter_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("add")),
        Some(&nat_tests::add_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("mul")),
        Some(&nat_tests::mul_definition())
    );
    assert!(loaded.theory().theorem(theorem("append_assoc")).is_none());
    assert!(
        loaded
            .theory()
            .theorem(theorem("add_computes_to_list"))
            .is_none()
    );
}

#[test]
fn theory_defines_reverse() {
    let theory = theory();
    let try_theory = try_theory().expect("prelude should load");

    assert_eq!(
        theory.computation(computation("reverse_acc")),
        Some(&list_tests::reverse_acc_definition())
    );
    assert_eq!(
        try_theory.computation(computation("reverse_acc")),
        Some(&list_tests::reverse_acc_definition())
    );
    assert_eq!(
        theory.computation(computation("reverse")),
        Some(&list_tests::reverse_definition())
    );
    assert_eq!(
        theory.computation(computation("append")),
        Some(&list_tests::append_definition())
    );
    assert_eq!(
        theory.computation(computation("snoc")),
        Some(&list_tests::snoc_definition())
    );
    assert_eq!(
        theory.computation(computation("concat")),
        Some(&list_tests::concat_definition())
    );
    assert_eq!(
        theory.computation(computation("length")),
        Some(&list_tests::length_definition())
    );
    assert_eq!(
        theory.computation(computation("take")),
        Some(&list_tests::take_definition())
    );
    assert_eq!(
        theory.computation(computation("drop")),
        Some(&list_tests::drop_definition())
    );
    assert_eq!(
        theory.computation(computation("split-at")),
        Some(&list_tests::split_at_definition())
    );
    assert_eq!(
        theory.computation(computation("nth")),
        Some(&list_tests::nth_definition())
    );
    assert_eq!(
        theory.computation(computation("replicate")),
        Some(&list_tests::replicate_definition())
    );
    assert_eq!(
        theory.computation(computation("intersperse")),
        Some(&list_tests::intersperse_definition())
    );
    assert_eq!(
        theory.computation(computation("intercalate")),
        Some(&list_tests::intercalate_definition())
    );
    assert_eq!(
        theory.computation(computation("map")),
        Some(&list_tests::map_definition())
    );
    assert_eq!(
        theory.computation(computation("concat-map")),
        Some(&list_tests::concat_map_definition())
    );
    assert_eq!(
        theory.computation(computation("fold-right")),
        Some(&list_tests::fold_right_definition())
    );
    assert_eq!(
        theory.computation(computation("fold-left")),
        Some(&list_tests::fold_left_definition())
    );
    assert_eq!(
        theory.computation(computation("zip")),
        Some(&list_tests::zip_definition())
    );
    assert_eq!(
        theory.computation(computation("unzip")),
        Some(&list_tests::unzip_definition())
    );
    assert_eq!(
        theory.computation(computation("zip-with")),
        Some(&list_tests::zip_with_definition())
    );
    assert_eq!(
        theory.computation(computation("filter")),
        Some(&list_tests::filter_definition())
    );
    assert_eq!(
        theory.computation(computation("partition")),
        Some(&list_tests::partition_definition())
    );
    assert_eq!(
        theory.computation(computation("any")),
        Some(&list_tests::any_definition())
    );
    assert_eq!(
        theory.computation(computation("all")),
        Some(&list_tests::all_definition())
    );
    assert_eq!(
        theory.computation(computation("find")),
        Some(&list_tests::find_definition())
    );
    assert_eq!(
        theory.computation(computation("not")),
        Some(&list_tests::bool_not_definition())
    );
    assert_eq!(
        theory.computation(computation("and")),
        Some(&list_tests::bool_and_definition())
    );
    assert_eq!(
        theory.computation(computation("or")),
        Some(&list_tests::bool_or_definition())
    );
    assert_eq!(
        theory.computation(computation("all-lists")),
        Some(&list_tests::all_lists_definition())
    );
    assert_eq!(
        theory.computation(computation("none")),
        Some(&list_tests::none_definition())
    );
    assert_eq!(
        theory.computation(computation("some")),
        Some(&list_tests::some_definition())
    );
    assert_eq!(
        theory.computation(computation("is-none")),
        Some(&list_tests::is_none_definition())
    );
    assert_eq!(
        theory.computation(computation("is-some")),
        Some(&list_tests::is_some_definition())
    );
    assert_eq!(
        theory.computation(computation("option-map")),
        Some(&list_tests::option_map_definition())
    );
    assert_eq!(
        theory.computation(computation("option-bind")),
        Some(&list_tests::option_bind_definition())
    );
    assert_eq!(
        theory.computation(computation("unwrap-or")),
        Some(&list_tests::unwrap_or_definition())
    );
    assert_eq!(
        theory.computation(computation("option-filter")),
        Some(&list_tests::option_filter_definition())
    );
    assert_eq!(
        theory.computation(computation("is-symbol")),
        Some(&list_tests::is_symbol_definition())
    );
    assert_eq!(
        theory.computation(computation("is-lambda")),
        Some(&list_tests::is_lambda_definition())
    );
    assert_eq!(
        theory.computation(computation("is-list-value")),
        Some(&list_tests::is_list_value_definition())
    );
    assert_eq!(
        theory.computation(computation("value-eq")),
        Some(&list_tests::value_eq_definition())
    );
    assert_eq!(
        theory.computation(computation("value-eq-comparable")),
        Some(&list_tests::value_eq_comparable_definition())
    );
    assert_eq!(
        theory.computation(computation("member")),
        Some(&list_tests::member_definition())
    );
    assert_eq!(
        theory.computation(computation("elem-index")),
        Some(&list_tests::elem_index_definition())
    );
    assert_eq!(
        theory.computation(computation("last")),
        Some(&list_tests::last_definition())
    );
    assert_eq!(
        theory.computation(computation("init")),
        Some(&list_tests::init_definition())
    );
    assert_eq!(
        theory.computation(computation("null")),
        Some(&list_tests::null_definition())
    );
    assert_eq!(
        theory.computation(computation("is-singleton")),
        Some(&list_tests::is_singleton_definition())
    );
    assert_eq!(
        theory.computation(computation("is-pair")),
        Some(&list_tests::is_pair_definition())
    );
    assert_eq!(
        theory.computation(computation("zero")),
        Some(&nat_tests::zero_definition())
    );
    assert_eq!(
        theory.computation(computation("succ")),
        Some(&nat_tests::succ_definition())
    );
    assert_eq!(
        theory.computation(computation("is-nat-value")),
        Some(&nat_tests::is_nat_value_definition())
    );
    assert_eq!(
        theory.computation(computation("is-zero")),
        Some(&nat_tests::is_zero_definition())
    );
    assert_eq!(
        theory.computation(computation("pred")),
        Some(&nat_tests::pred_definition())
    );
    assert_eq!(
        theory.computation(computation("range")),
        Some(&nat_tests::range_definition())
    );
    assert_eq!(
        theory.computation(computation("add")),
        Some(&nat_tests::add_definition())
    );
    assert_eq!(
        theory.computation(computation("mul")),
        Some(&nat_tests::mul_definition())
    );
    assert_eq!(reverse_acc(), Computation::Ref(computation("reverse_acc")));
    assert_eq!(reverse(), Computation::Ref(computation("reverse")));
    assert_eq!(append(), Computation::Ref(computation("append")));
    assert_eq!(snoc(), Computation::Ref(computation("snoc")));
    assert_eq!(concat(), Computation::Ref(computation("concat")));
    assert_eq!(length(), Computation::Ref(computation("length")));
    assert_eq!(take(), Computation::Ref(computation("take")));
    assert_eq!(drop(), Computation::Ref(computation("drop")));
    assert_eq!(split_at(), Computation::Ref(computation("split-at")));
    assert_eq!(nth(), Computation::Ref(computation("nth")));
    assert_eq!(replicate(), Computation::Ref(computation("replicate")));
    assert_eq!(intersperse(), Computation::Ref(computation("intersperse")));
    assert_eq!(intercalate(), Computation::Ref(computation("intercalate")));
    assert_eq!(map(), Computation::Ref(computation("map")));
    assert_eq!(concat_map(), Computation::Ref(computation("concat-map")));
    assert_eq!(fold_right(), Computation::Ref(computation("fold-right")));
    assert_eq!(fold_left(), Computation::Ref(computation("fold-left")));
    assert_eq!(zip(), Computation::Ref(computation("zip")));
    assert_eq!(unzip(), Computation::Ref(computation("unzip")));
    assert_eq!(zip_with(), Computation::Ref(computation("zip-with")));
    assert_eq!(filter(), Computation::Ref(computation("filter")));
    assert_eq!(partition(), Computation::Ref(computation("partition")));
    assert_eq!(any(), Computation::Ref(computation("any")));
    assert_eq!(all(), Computation::Ref(computation("all")));
    assert_eq!(find(), Computation::Ref(computation("find")));
    assert_eq!(bool_not(), Computation::Ref(computation("not")));
    assert_eq!(bool_and(), Computation::Ref(computation("and")));
    assert_eq!(bool_or(), Computation::Ref(computation("or")));
    assert_eq!(all_lists(), Computation::Ref(computation("all-lists")));
    assert_eq!(none(), Computation::Ref(computation("none")));
    assert_eq!(some(), Computation::Ref(computation("some")));
    assert_eq!(is_none(), Computation::Ref(computation("is-none")));
    assert_eq!(is_some(), Computation::Ref(computation("is-some")));
    assert_eq!(option_map(), Computation::Ref(computation("option-map")));
    assert_eq!(option_bind(), Computation::Ref(computation("option-bind")));
    assert_eq!(unwrap_or(), Computation::Ref(computation("unwrap-or")));
    assert_eq!(
        option_filter(),
        Computation::Ref(computation("option-filter"))
    );
    assert_eq!(is_symbol(), Computation::Ref(computation("is-symbol")));
    assert_eq!(is_lambda(), Computation::Ref(computation("is-lambda")));
    assert_eq!(
        is_list_value(),
        Computation::Ref(computation("is-list-value"))
    );
    assert_eq!(value_eq(), Computation::Ref(computation("value-eq")));
    assert_eq!(
        value_eq_comparable(),
        Computation::Ref(computation("value-eq-comparable"))
    );
    assert_eq!(member(), Computation::Ref(computation("member")));
    assert_eq!(elem_index(), Computation::Ref(computation("elem-index")));
    assert_eq!(last(), Computation::Ref(computation("last")));
    assert_eq!(init(), Computation::Ref(computation("init")));
    assert_eq!(null(), Computation::Ref(computation("null")));
    assert_eq!(
        is_singleton(),
        Computation::Ref(computation("is-singleton"))
    );
    assert_eq!(is_pair(), Computation::Ref(computation("is-pair")));
    assert_eq!(zero(), Computation::Ref(computation("zero")));
    assert_eq!(succ(), Computation::Ref(computation("succ")));
    assert_eq!(
        is_nat_value(),
        Computation::Ref(computation("is-nat-value"))
    );
    assert_eq!(range(), Computation::Ref(computation("range")));
    assert_eq!(add(), Computation::Ref(computation("add")));
    assert_eq!(
        theory.reduce(&reverse_acc()),
        Step::Reduced(list_tests::reverse_acc_definition())
    );
    assert_eq!(
        theory.reduce(&reverse()),
        Step::Reduced(list_tests::reverse_definition())
    );
    assert_eq!(
        theory.reduce(&append()),
        Step::Reduced(list_tests::append_definition())
    );
    assert_eq!(
        theory.reduce(&snoc()),
        Step::Reduced(list_tests::snoc_definition())
    );
    assert_eq!(
        theory.reduce(&concat()),
        Step::Reduced(list_tests::concat_definition())
    );
    assert_eq!(
        theory.reduce(&length()),
        Step::Reduced(list_tests::length_definition())
    );
    assert_eq!(
        theory.reduce(&take()),
        Step::Reduced(list_tests::take_definition())
    );
    assert_eq!(
        theory.reduce(&drop()),
        Step::Reduced(list_tests::drop_definition())
    );
    assert_eq!(
        theory.reduce(&split_at()),
        Step::Reduced(list_tests::split_at_definition())
    );
    assert_eq!(
        theory.reduce(&nth()),
        Step::Reduced(list_tests::nth_definition())
    );
    assert_eq!(
        theory.reduce(&replicate()),
        Step::Reduced(list_tests::replicate_definition())
    );
    assert_eq!(
        theory.reduce(&intersperse()),
        Step::Reduced(list_tests::intersperse_definition())
    );
    assert_eq!(
        theory.reduce(&intercalate()),
        Step::Reduced(list_tests::intercalate_definition())
    );
    assert_eq!(
        theory.reduce(&map()),
        Step::Reduced(list_tests::map_definition())
    );
    assert_eq!(
        theory.reduce(&concat_map()),
        Step::Reduced(list_tests::concat_map_definition())
    );
    assert_eq!(
        theory.reduce(&fold_right()),
        Step::Reduced(list_tests::fold_right_definition())
    );
    assert_eq!(
        theory.reduce(&fold_left()),
        Step::Reduced(list_tests::fold_left_definition())
    );
    assert_eq!(
        theory.reduce(&zip()),
        Step::Reduced(list_tests::zip_definition())
    );
    assert_eq!(
        theory.reduce(&unzip()),
        Step::Reduced(list_tests::unzip_definition())
    );
    assert_eq!(
        theory.reduce(&zip_with()),
        Step::Reduced(list_tests::zip_with_definition())
    );
    assert_eq!(
        theory.reduce(&filter()),
        Step::Reduced(list_tests::filter_definition())
    );
    assert_eq!(
        theory.reduce(&partition()),
        Step::Reduced(list_tests::partition_definition())
    );
    assert_eq!(
        theory.reduce(&any()),
        Step::Reduced(list_tests::any_definition())
    );
    assert_eq!(
        theory.reduce(&all()),
        Step::Reduced(list_tests::all_definition())
    );
    assert_eq!(
        theory.reduce(&find()),
        Step::Reduced(list_tests::find_definition())
    );
    assert_eq!(
        theory.reduce(&bool_not()),
        Step::Reduced(list_tests::bool_not_definition())
    );
    assert_eq!(
        theory.reduce(&bool_and()),
        Step::Reduced(list_tests::bool_and_definition())
    );
    assert_eq!(
        theory.reduce(&bool_or()),
        Step::Reduced(list_tests::bool_or_definition())
    );
    assert_eq!(
        theory.reduce(&all_lists()),
        Step::Reduced(list_tests::all_lists_definition())
    );
    assert_eq!(
        theory.reduce(&none()),
        Step::Reduced(list_tests::none_definition())
    );
    assert_eq!(
        theory.reduce(&some()),
        Step::Reduced(list_tests::some_definition())
    );
    assert_eq!(
        theory.reduce(&is_none()),
        Step::Reduced(list_tests::is_none_definition())
    );
    assert_eq!(
        theory.reduce(&is_some()),
        Step::Reduced(list_tests::is_some_definition())
    );
    assert_eq!(
        theory.reduce(&option_map()),
        Step::Reduced(list_tests::option_map_definition())
    );
    assert_eq!(
        theory.reduce(&option_bind()),
        Step::Reduced(list_tests::option_bind_definition())
    );
    assert_eq!(
        theory.reduce(&unwrap_or()),
        Step::Reduced(list_tests::unwrap_or_definition())
    );
    assert_eq!(
        theory.reduce(&option_filter()),
        Step::Reduced(list_tests::option_filter_definition())
    );
    assert_eq!(
        theory.reduce(&is_symbol()),
        Step::Reduced(list_tests::is_symbol_definition())
    );
    assert_eq!(
        theory.reduce(&is_lambda()),
        Step::Reduced(list_tests::is_lambda_definition())
    );
    assert_eq!(
        theory.reduce(&is_list_value()),
        Step::Reduced(list_tests::is_list_value_definition())
    );
    assert_eq!(
        theory.reduce(&value_eq()),
        Step::Reduced(list_tests::value_eq_definition())
    );
    assert_eq!(
        theory.reduce(&value_eq_comparable()),
        Step::Reduced(list_tests::value_eq_comparable_definition())
    );
    assert_eq!(
        theory.reduce(&member()),
        Step::Reduced(list_tests::member_definition())
    );
    assert_eq!(
        theory.reduce(&elem_index()),
        Step::Reduced(list_tests::elem_index_definition())
    );
    assert_eq!(
        theory.reduce(&last()),
        Step::Reduced(list_tests::last_definition())
    );
    assert_eq!(
        theory.reduce(&init()),
        Step::Reduced(list_tests::init_definition())
    );
    assert_eq!(
        theory.reduce(&null()),
        Step::Reduced(list_tests::null_definition())
    );
    assert_eq!(
        theory.reduce(&is_singleton()),
        Step::Reduced(list_tests::is_singleton_definition())
    );
    assert_eq!(
        theory.reduce(&is_pair()),
        Step::Reduced(list_tests::is_pair_definition())
    );
    assert_eq!(
        theory.reduce(&zero()),
        Step::Reduced(nat_tests::zero_definition())
    );
    assert_eq!(
        theory.reduce(&succ()),
        Step::Reduced(nat_tests::succ_definition())
    );
    assert_eq!(
        theory.reduce(&is_nat_value()),
        Step::Reduced(nat_tests::is_nat_value_definition())
    );
    assert_eq!(
        theory.reduce(&is_zero()),
        Step::Reduced(nat_tests::is_zero_definition())
    );
    assert_eq!(
        theory.reduce(&pred()),
        Step::Reduced(nat_tests::pred_definition())
    );
    assert_eq!(
        theory.reduce(&range()),
        Step::Reduced(nat_tests::range_definition())
    );
    assert_eq!(
        theory.reduce(&add()),
        Step::Reduced(nat_tests::add_definition())
    );
    assert_eq!(
        theory.reduce(&mul()),
        Step::Reduced(nat_tests::mul_definition())
    );
}

#[test]
fn computation_theory_does_not_define_theorems() {
    let theory = computation_theory();
    let try_theory = try_computation_theory().expect("prelude computations should load");

    for theorem in prelude_theorem_names() {
        assert!(theory.theorem(theorem).is_none());
        assert!(try_theory.theorem(theorem).is_none());
    }
}

#[test]
fn computation_definition_diagnostics_report_kernel_rejection() {
    let mut theory = Theory::new();

    assert!(theory.define_computation(computation("reverse_acc"), &Computation::Nil));
    assert!(!define_computations_in_theory(&mut theory));
    assert_eq!(
        try_define_computations_in_theory(&mut theory),
        Err(SourceComputationError::ComputationRejected {
            section: Some(SourceSection::new("list/core")),
            computation: computation("reverse_acc"),
            error: ComputationDefinitionError::ComputationNameAlreadyDefined(computation(
                "reverse_acc"
            )),
        })
    );
}

#[test]
fn full_source_load_diagnostics_report_computation_failures() {
    let mut theory = Theory::new();

    assert!(theory.define_computation(computation("reverse_acc"), &Computation::Nil));
    assert!(!define_in_theory(&mut theory));
    assert_eq!(
        try_define_in_theory(&mut theory),
        Err(SourceLoadError::Computation(
            SourceComputationError::ComputationRejected {
                section: Some(SourceSection::new("list/core")),
                computation: computation("reverse_acc"),
                error: ComputationDefinitionError::ComputationNameAlreadyDefined(computation(
                    "reverse_acc"
                )),
            }
        ))
    );
}

#[test]
fn theorem_definitions_require_computations() {
    let mut quick_check_theory = Theory::new();
    assert!(!define_theorems_in_theory(&mut quick_check_theory));

    let mut theory = Theory::new();

    let theorem_result = try_define_theorems_in_theory(&mut theory);
    let Err(SourceTheoremError::ProofElaborationFailed {
        section,
        theorem: failed_theorem,
        error,
    }) = theorem_result
    else {
        panic!("theorem loading should report proof elaboration failure, got {theorem_result:?}");
    };
    assert_eq!(failed_theorem, theorem("not_true"), "{error:?}");
    assert_eq!(section, Some(SourceSection::new("list/booleans")));
    assert!(proof_error_contains_evaluation_failure(&error));

    let computation_independent_theorems = [
        theorem("if_true"),
        theorem("if_false"),
        theorem("if_condition_true"),
        theorem("if_condition_false"),
        theorem("if_true_result_with_false_else"),
        theorem("if_true_result_with_error_then"),
        theorem("if_true_result_with_false_then"),
        theorem("if_false_result_with_true_then"),
        theorem("if_false_result_with_true_else"),
        theorem("if_false_result_with_error_else"),
        theorem("if_false_result_with_false_else"),
        theorem("if_true_result_with_true_then"),
        theorem("if_true_result_with_true_else"),
        theorem("if_false_result_with_false_then"),
        theorem("symbol_eq_unit_unit"),
        theorem("symbol_eq_true_false"),
        theorem("symbol_eq_true"),
        theorem("symbol_eq_true_implies_is_symbol_left"),
        theorem("symbol_eq_true_implies_is_symbol_right"),
        theorem("symbol_eq_false_distinct"),
        theorem("symbol_eq_symm"),
        theorem("symbol_eq_refl"),
        theorem("symbol_eq_computes_to_bool"),
        theorem("true_is_bool"),
        theorem("false_is_bool"),
        theorem("is_bool_elim"),
        theorem("bool_distinct"),
    ];
    for theorem in computation_independent_theorems {
        assert!(theory.theorem(theorem).is_some());
    }

    for theorem in prelude_theorem_names() {
        if !computation_independent_theorems.contains(&theorem) {
            assert!(theory.theorem(theorem).is_none());
        }
    }
}

#[test]
fn full_source_load_diagnostics_report_theorem_failures() {
    let (module, env) = parse_test_module(
        "
            (theorem bad
              (equal nil (quote unit))
              (proof (eval-to nil nil)))
            ",
    );
    let bad = env
        .theorem("bad")
        .expect("module should define bad theorem");
    let mut theory = Theory::new();

    assert_eq!(
        define_module_in_theory_result(&mut theory, &module),
        Err(SourceLoadError::Theorem(
            SourceTheoremError::TheoremRejected {
                section: None,
                theorem: bad,
                error: TheoremError::InvalidProof,
            }
        ))
    );
}

fn proof_error_contains_evaluation_failure(error: &ProofElaborationError) -> bool {
    match error {
        ProofElaborationError::EvaluationFailed(_) => true,
        ProofElaborationError::InSubproof { error, .. } => {
            proof_error_contains_evaluation_failure(error)
        }
        ProofElaborationError::UnknownTheorem(_) => false,
        ProofElaborationError::TacticFailed { .. } => false,
    }
}

#[test]
fn source_theorem_diagnostics_report_kernel_rejection() {
    let (module, env) = parse_test_module(
        "
            (theorem bad
              (equal nil (quote unit))
              (proof (eval-to nil nil)))
            ",
    );
    let bad = env
        .theorem("bad")
        .expect("module should define bad theorem");

    assert_eq!(
        proof::source_theorem_result(module, bad, Theory::new()),
        Err(SourceTheoremError::TheoremRejected {
            section: None,
            theorem: bad,
            error: TheoremError::InvalidProof,
        })
    );
}

#[test]
fn source_theorem_diagnostics_report_unknown_known_theorem() {
    let (module, env) = parse_test_module(
        "
            (theorem bad
              (equal nil nil)
              (proof (known later)))
            (theorem later
              (equal nil nil)
              (proof (eval-to nil nil)))
            ",
    );
    let bad = env
        .theorem("bad")
        .expect("module should define bad theorem");
    let later = env
        .theorem("later")
        .expect("module should define later theorem");

    assert_eq!(
        proof::source_theorem_result(module, bad, Theory::new()),
        Err(SourceTheoremError::ProofElaborationFailed {
            section: None,
            theorem: bad,
            error: ProofElaborationError::UnknownTheorem(later),
        })
    );
}

#[test]
fn theory_defines_reverse_theorems() {
    let theory = theory();
    let nil_is_list_prop = list_tests::nil_is_list_source_theorem();
    let cons_is_list_prop = list_tests::cons_is_list_source_theorem();
    let cons_head_prop = list_tests::cons_head_source_theorem();
    let cons_tail_prop = list_tests::cons_tail_source_theorem();
    let nil_not_cons_prop = list_tests::nil_not_cons_source_theorem();
    let cons_not_nil_prop = list_tests::cons_not_nil_source_theorem();
    let cons_injective_head_prop = list_tests::cons_injective_head_source_theorem();
    let cons_injective_tail_prop = list_tests::cons_injective_tail_source_theorem();
    let cons_injective_prop = list_tests::cons_injective_source_theorem();
    let list_eta_prop = list_tests::list_eta_source_theorem();
    let reverse_acc_prop = list_tests::reverse_acc_computes_to_list_source_theorem();
    let reverse_prop = list_tests::reverse_computes_to_list_source_theorem();
    let reverse_nil_prop = list_tests::reverse_nil_computes_to_list_source_theorem();
    let reverse_nil_exact_prop = list_tests::reverse_nil_source_theorem();
    let reverse_singleton_prop = list_tests::reverse_singleton_source_theorem();
    let reverse_congr_prop = list_tests::reverse_congr_source_theorem();
    let reverse_acc_append_prop = list_tests::reverse_acc_append_source_theorem();
    let reverse_cons_prop = list_tests::reverse_cons_source_theorem();
    let reverse_acc_reverse_prop = list_tests::reverse_acc_reverse_source_theorem();
    let reverse_double_prop = list_tests::reverse_double_source_theorem();
    let reverse_acc_of_append_prop = list_tests::reverse_acc_of_append_source_theorem();
    let reverse_append_prop = list_tests::reverse_append_source_theorem();
    let map_reverse_prop = list_tests::map_reverse_source_theorem();
    let snoc_prop = list_tests::snoc_computes_to_list_source_theorem();
    let snoc_nil_prop = list_tests::snoc_nil_source_theorem();
    let snoc_cons_prop = list_tests::snoc_cons_source_theorem();
    let member_snoc_prop = list_tests::member_snoc_source_theorem();
    let tail_snoc_after_snoc_prop = list_tests::tail_snoc_after_snoc_source_theorem();
    let all_lists_snoc_prop = list_tests::all_lists_snoc_source_theorem();
    let concat_nil_prop = list_tests::concat_nil_source_theorem();
    let concat_cons_prop = list_tests::concat_cons_source_theorem();
    let concat_computes_to_list_prop = list_tests::concat_computes_to_list_source_theorem();
    let concat_append_prop = list_tests::concat_append_source_theorem();
    let map_length_nil_prop = list_tests::map_length_nil_source_theorem();
    let map_length_cons_prop = list_tests::map_length_cons_source_theorem();
    let map_length_computes_to_list_prop = list_tests::map_length_computes_to_list_source_theorem();
    let length_concat_prop = list_tests::length_concat_source_theorem();
    let length_nil_prop = list_tests::length_nil_source_theorem();
    let length_cons_prop = list_tests::length_cons_source_theorem();
    let length_singleton_prop = list_tests::length_singleton_source_theorem();
    let length_computes_to_list_prop = list_tests::length_computes_to_list_source_theorem();
    let length_append_prop = list_tests::length_append_source_theorem();
    let append_length_singleton_prop = list_tests::append_length_singleton_source_theorem();
    let length_snoc_prop = list_tests::length_snoc_source_theorem();
    let length_take_prop = list_tests::length_take_source_theorem();
    let length_drop_prop = list_tests::length_drop_source_theorem();
    let length_take_add_length_drop_prop = list_tests::length_take_add_length_drop_source_theorem();
    let length_reverse_prop = list_tests::length_reverse_source_theorem();
    let take_zero_prop = list_tests::take_zero_source_theorem();
    let take_nil_prop = list_tests::take_nil_source_theorem();
    let take_cons_prop = list_tests::take_cons_source_theorem();
    let take_computes_to_list_prop = list_tests::take_computes_to_list_source_theorem();
    let take_congr_count_computation_prop =
        list_tests::take_congr_count_computation_source_theorem();
    let take_congr_list_computation_prop = list_tests::take_congr_list_computation_source_theorem();
    let drop_zero_prop = list_tests::drop_zero_source_theorem();
    let drop_nil_prop = list_tests::drop_nil_source_theorem();
    let drop_cons_prop = list_tests::drop_cons_source_theorem();
    let drop_computes_to_list_prop = list_tests::drop_computes_to_list_source_theorem();
    let drop_congr_count_computation_prop =
        list_tests::drop_congr_count_computation_source_theorem();
    let drop_congr_list_computation_prop = list_tests::drop_congr_list_computation_source_theorem();
    let take_take_prop = list_tests::take_take_source_theorem();
    let drop_drop_prop = list_tests::drop_drop_source_theorem();
    let take_drop_commute_prop = list_tests::take_drop_commute_source_theorem();
    let split_at_def_prop = list_tests::split_at_def_source_theorem();
    let split_at_zero_prop = list_tests::split_at_zero_source_theorem();
    let split_at_nil_prop = list_tests::split_at_nil_source_theorem();
    let split_at_cons_prop = list_tests::split_at_cons_source_theorem();
    let split_at_computes_to_pair_prop = list_tests::split_at_computes_to_pair_source_theorem();
    let split_at_first_take_prop = list_tests::split_at_first_take_source_theorem();
    let split_at_second_drop_prop = list_tests::split_at_second_drop_source_theorem();
    let nth_zero_nil_prop = list_tests::nth_zero_nil_source_theorem();
    let nth_zero_cons_prop = list_tests::nth_zero_cons_source_theorem();
    let nth_cons_nil_prop = list_tests::nth_cons_nil_source_theorem();
    let nth_cons_cons_prop = list_tests::nth_cons_cons_source_theorem();
    let nth_zero_cons_some_prop = list_tests::nth_zero_cons_some_source_theorem();
    let nth_out_of_bounds_none_prop = list_tests::nth_out_of_bounds_none_source_theorem();
    let nth_computes_to_option_prop = list_tests::nth_computes_to_option_source_theorem();
    let replicate_zero_prop = list_tests::replicate_zero_source_theorem();
    let replicate_cons_prop = list_tests::replicate_cons_source_theorem();
    let replicate_computes_to_list_prop = list_tests::replicate_computes_to_list_source_theorem();
    let length_replicate_prop = list_tests::length_replicate_source_theorem();
    let take_replicate_prop = list_tests::take_replicate_source_theorem();
    let drop_replicate_prop = list_tests::drop_replicate_source_theorem();
    let intersperse_nil_prop = list_tests::intersperse_nil_source_theorem();
    let intersperse_singleton_prop = list_tests::intersperse_singleton_source_theorem();
    let intersperse_cons_cons_prop = list_tests::intersperse_cons_cons_source_theorem();
    let intersperse_cons_computes_to_list_prop =
        list_tests::intersperse_cons_computes_to_list_source_theorem();
    let intersperse_computes_to_list_prop =
        list_tests::intersperse_computes_to_list_source_theorem();
    let intercalate_nil_prop = list_tests::intercalate_nil_source_theorem();
    let intercalate_singleton_prop = list_tests::intercalate_singleton_source_theorem();
    let intercalate_cons_cons_prop = list_tests::intercalate_cons_cons_source_theorem();
    let is_list_value_true_implies_is_list_prop =
        list_tests::is_list_value_true_implies_is_list_source_theorem();
    let value_kind_list_implies_is_list_prop =
        list_tests::value_kind_list_implies_is_list_source_theorem();
    let is_list_implies_is_list_value_true_prop =
        list_tests::is_list_implies_is_list_value_true_source_theorem();
    let all_lists_cons_prop = list_tests::all_lists_cons_source_theorem();
    let all_lists_cons_true_prop = list_tests::all_lists_cons_true_source_theorem();
    let symbol_eq_refl_prop = list_tests::symbol_eq_refl_source_theorem();
    let symbol_eq_true_implies_is_symbol_left_prop =
        list_tests::symbol_eq_true_implies_is_symbol_left_source_theorem();
    let symbol_eq_true_implies_is_symbol_right_prop =
        list_tests::symbol_eq_true_implies_is_symbol_right_source_theorem();
    let symbol_eq_false_distinct_prop = list_tests::symbol_eq_false_distinct_source_theorem();
    let symbol_eq_symm_prop = list_tests::symbol_eq_symm_source_theorem();
    let symbol_eq_computes_to_bool_prop = list_tests::symbol_eq_computes_to_bool_source_theorem();
    let true_is_bool_prop = list_tests::true_is_bool_source_theorem();
    let false_is_bool_prop = list_tests::false_is_bool_source_theorem();
    let is_bool_elim_prop = list_tests::is_bool_elim_source_theorem();
    let bool_distinct_prop = list_tests::bool_distinct_source_theorem();
    let not_congr_prop = list_tests::not_congr_source_theorem();
    let and_congr_left_prop = list_tests::and_congr_left_source_theorem();
    let and_congr_right_prop = list_tests::and_congr_right_source_theorem();
    let and_congr_prop = list_tests::and_congr_source_theorem();
    let or_congr_left_prop = list_tests::or_congr_left_source_theorem();
    let or_congr_right_prop = list_tests::or_congr_right_source_theorem();
    let or_congr_prop = list_tests::or_congr_source_theorem();
    let not_true_elim_prop = list_tests::not_true_elim_source_theorem();
    let not_false_elim_prop = list_tests::not_false_elim_source_theorem();
    let if_computes_to_bool_prop = list_tests::if_computes_to_bool_source_theorem();
    let if_same_prop = list_tests::if_same_source_theorem();
    let if_not_prop = list_tests::if_not_source_theorem();
    let if_congr_condition_prop = list_tests::if_congr_condition_source_theorem();
    let if_congr_then_prop = list_tests::if_congr_then_source_theorem();
    let if_congr_else_prop = list_tests::if_congr_else_source_theorem();
    let if_false_result_with_true_else_prop =
        list_tests::if_false_result_with_true_else_source_theorem();
    let if_false_result_with_error_else_prop =
        list_tests::if_false_result_with_error_else_source_theorem();
    let if_false_result_with_false_else_prop =
        list_tests::if_false_result_with_false_else_source_theorem();
    let if_true_result_with_true_then_prop =
        list_tests::if_true_result_with_true_then_source_theorem();
    let if_true_result_with_true_else_prop =
        list_tests::if_true_result_with_true_else_source_theorem();
    let if_false_result_with_false_then_prop =
        list_tests::if_false_result_with_false_then_source_theorem();
    let and_true_intro_prop = list_tests::and_true_intro_source_theorem();
    let and_true_elim_left_prop = list_tests::and_true_elim_left_source_theorem();
    let and_true_elim_right_prop = list_tests::and_true_elim_right_source_theorem();
    let and_false_cases_prop = list_tests::and_false_cases_source_theorem();
    let or_false_intro_prop = list_tests::or_false_intro_source_theorem();
    let or_false_elim_left_prop = list_tests::or_false_elim_left_source_theorem();
    let or_false_elim_right_prop = list_tests::or_false_elim_right_source_theorem();
    let or_true_cases_prop = list_tests::or_true_cases_source_theorem();
    let and_prop_to_bool_prop = list_tests::and_prop_to_bool_source_theorem();
    let and_bool_to_prop_prop = list_tests::and_bool_to_prop_source_theorem();
    let or_prop_to_bool_left_prop = list_tests::or_prop_to_bool_left_source_theorem();
    let or_prop_to_bool_right_prop = list_tests::or_prop_to_bool_right_source_theorem();
    let or_bool_to_prop_prop = list_tests::or_bool_to_prop_source_theorem();
    let not_bool_to_absurd_prop = list_tests::not_bool_to_absurd_source_theorem();
    let not_absurd_to_bool_false_prop = list_tests::not_absurd_to_bool_false_source_theorem();
    let and_absorb_or_prop = list_tests::and_absorb_or_source_theorem();
    let or_absorb_and_prop = list_tests::or_absorb_and_source_theorem();
    let and_distrib_or_left_prop = list_tests::and_distrib_or_left_source_theorem();
    let and_distrib_or_right_prop = list_tests::and_distrib_or_right_source_theorem();
    let or_distrib_and_left_prop = list_tests::or_distrib_and_left_source_theorem();
    let or_distrib_and_right_prop = list_tests::or_distrib_and_right_source_theorem();
    let not_and_prop = list_tests::not_and_source_theorem();
    let not_or_prop = list_tests::not_or_source_theorem();
    let none_is_none_prop = list_tests::none_is_none_source_theorem();
    let some_is_none_prop = list_tests::some_is_none_source_theorem();
    let none_is_some_prop = list_tests::none_is_some_source_theorem();
    let some_is_some_prop = list_tests::some_is_some_source_theorem();
    let some_congr_prop = list_tests::some_congr_source_theorem();
    let some_injective_prop = list_tests::some_injective_source_theorem();
    let option_map_none_prop = list_tests::option_map_none_source_theorem();
    let option_map_some_prop = list_tests::option_map_some_source_theorem();
    let option_bind_none_prop = list_tests::option_bind_none_source_theorem();
    let option_bind_some_prop = list_tests::option_bind_some_source_theorem();
    let unwrap_or_none_prop = list_tests::unwrap_or_none_source_theorem();
    let unwrap_or_some_prop = list_tests::unwrap_or_some_source_theorem();
    let option_filter_none_prop = list_tests::option_filter_none_source_theorem();
    let option_filter_some_true_prop = list_tests::option_filter_some_true_source_theorem();
    let option_filter_some_false_prop = list_tests::option_filter_some_false_source_theorem();
    let option_map_computes_to_option_prop =
        list_tests::option_map_computes_to_option_source_theorem();
    let option_bind_computes_to_option_prop =
        list_tests::option_bind_computes_to_option_source_theorem();
    let unwrap_or_computes_to_value_prop = list_tests::unwrap_or_computes_to_value_source_theorem();
    let option_filter_computes_to_option_prop =
        list_tests::option_filter_computes_to_option_source_theorem();
    let option_map_identity_prop = list_tests::option_map_identity_source_theorem();
    let option_map_compose_prop = list_tests::option_map_compose_source_theorem();
    let option_bind_left_identity_prop = list_tests::option_bind_left_identity_source_theorem();
    let option_bind_right_identity_prop = list_tests::option_bind_right_identity_source_theorem();
    let option_bind_assoc_prop = list_tests::option_bind_assoc_source_theorem();
    let option_map_congr_function_prop = list_tests::option_map_congr_function_source_theorem();
    let option_map_congr_option_prop = list_tests::option_map_congr_option_source_theorem();
    let option_map_congr_option_computation_prop =
        list_tests::option_map_congr_option_computation_source_theorem();
    let option_map_congr_prop = list_tests::option_map_congr_source_theorem();
    let option_bind_congr_function_prop = list_tests::option_bind_congr_function_source_theorem();
    let option_bind_congr_option_prop = list_tests::option_bind_congr_option_source_theorem();
    let option_bind_congr_option_computation_prop =
        list_tests::option_bind_congr_option_computation_source_theorem();
    let unwrap_or_congr_default_prop = list_tests::unwrap_or_congr_default_source_theorem();
    let unwrap_or_congr_option_prop = list_tests::unwrap_or_congr_option_source_theorem();
    let pair_first_prop = list_tests::pair_first_source_theorem();
    let pair_tail_prop = list_tests::pair_tail_source_theorem();
    let pair_second_prop = list_tests::pair_second_source_theorem();
    let pair_computes_to_list_prop = list_tests::pair_computes_to_list_source_theorem();
    let pair_computes_to_value_prop = list_tests::pair_computes_to_value_source_theorem();
    let pair_eta_prop = list_tests::pair_eta_source_theorem();
    let pair_congr_prop = list_tests::pair_congr_source_theorem();
    let pair_first_from_computation_prop = list_tests::pair_first_from_computation_source_theorem();
    let pair_second_from_computation_prop =
        list_tests::pair_second_from_computation_source_theorem();
    let pair_injective_first_prop = list_tests::pair_injective_first_source_theorem();
    let pair_injective_second_prop = list_tests::pair_injective_second_source_theorem();
    let pair_injective_prop = list_tests::pair_injective_source_theorem();
    let list_pair_first_from_computation_prop =
        list_tests::list_pair_first_from_computation_source_theorem();
    let list_pair_second_from_computation_prop =
        list_tests::list_pair_second_from_computation_source_theorem();
    let intercalate_cons_computes_to_list_prop =
        list_tests::intercalate_cons_computes_to_list_source_theorem();
    let intercalate_computes_to_list_prop =
        list_tests::intercalate_computes_to_list_source_theorem();
    let map_nil_prop = list_tests::map_nil_source_theorem();
    let map_cons_prop = list_tests::map_cons_source_theorem();
    let map_computes_to_list_prop = list_tests::map_computes_to_list_source_theorem();
    let length_map_prop = list_tests::length_map_source_theorem();
    let map_replicate_prop = list_tests::map_replicate_source_theorem();
    let concat_map_nil_prop = list_tests::concat_map_nil_source_theorem();
    let concat_map_cons_prop = list_tests::concat_map_cons_source_theorem();
    let concat_map_computes_to_list_prop = list_tests::concat_map_computes_to_list_source_theorem();
    let fold_right_nil_prop = list_tests::fold_right_nil_source_theorem();
    let fold_right_cons_prop = list_tests::fold_right_cons_source_theorem();
    let fold_right_computes_to_value_prop =
        list_tests::fold_right_computes_to_value_source_theorem();
    let fold_right_congr_prop = list_tests::fold_right_congr_source_theorem();
    let fold_left_nil_prop = list_tests::fold_left_nil_source_theorem();
    let fold_left_cons_prop = list_tests::fold_left_cons_source_theorem();
    let fold_left_computes_to_value_prop = list_tests::fold_left_computes_to_value_source_theorem();
    let fold_left_congr_prop = list_tests::fold_left_congr_source_theorem();
    let append_take_drop_prop = list_tests::append_take_drop_source_theorem();
    let zip_left_nil_prop = list_tests::zip_left_nil_source_theorem();
    let zip_right_nil_prop = list_tests::zip_right_nil_source_theorem();
    let zip_cons_prop = list_tests::zip_cons_source_theorem();
    let zip_computes_to_list_prop = list_tests::zip_computes_to_list_source_theorem();
    let zip_pair_shape_prop = list_tests::zip_pair_shape_source_theorem();
    let unzip_nil_prop = list_tests::unzip_nil_source_theorem();
    let unzip_cons_prop = list_tests::unzip_cons_source_theorem();
    let unzip_pair_shape_prop = list_tests::unzip_pair_shape_source_theorem();
    let zip_unzip_prop = list_tests::zip_unzip_source_theorem();
    let unzip_zip_prop = list_tests::unzip_zip_source_theorem();
    let zip_with_as_map_zip_prop = list_tests::zip_with_as_map_zip_source_theorem();
    let zip_with_left_nil_prop = list_tests::zip_with_left_nil_source_theorem();
    let zip_with_right_nil_prop = list_tests::zip_with_right_nil_source_theorem();
    let zip_with_cons_prop = list_tests::zip_with_cons_source_theorem();
    let zip_with_computes_to_list_prop = list_tests::zip_with_computes_to_list_source_theorem();
    let filter_nil_prop = list_tests::filter_nil_source_theorem();
    let filter_cons_true_prop = list_tests::filter_cons_true_source_theorem();
    let filter_cons_false_prop = list_tests::filter_cons_false_source_theorem();
    let filter_computes_to_list_prop = list_tests::filter_computes_to_list_source_theorem();
    let filter_congr_prop = list_tests::filter_congr_source_theorem();
    let reject_nil_prop = list_tests::reject_nil_source_theorem();
    let reject_cons_true_prop = list_tests::reject_cons_true_source_theorem();
    let reject_cons_false_prop = list_tests::reject_cons_false_source_theorem();
    let reject_computes_to_list_prop = list_tests::reject_computes_to_list_source_theorem();
    let filter_append_prop = list_tests::filter_append_source_theorem();
    let reject_append_prop = list_tests::reject_append_source_theorem();
    let filter_idempotent_prop = list_tests::filter_idempotent_source_theorem();
    let reject_idempotent_prop = list_tests::reject_idempotent_source_theorem();
    let partition_nil_prop = list_tests::partition_nil_source_theorem();
    let partition_cons_true_prop = list_tests::partition_cons_true_source_theorem();
    let partition_cons_false_prop = list_tests::partition_cons_false_source_theorem();
    let partition_computes_to_pair_prop = list_tests::partition_computes_to_pair_source_theorem();
    let partition_first_filter_prop = list_tests::partition_first_filter_source_theorem();
    let partition_second_filter_false_prop =
        list_tests::partition_second_filter_false_source_theorem();
    let partition_second_reject_prop = list_tests::partition_second_reject_source_theorem();
    let any_nil_prop = list_tests::any_nil_source_theorem();
    let any_cons_true_prop = list_tests::any_cons_true_source_theorem();
    let any_cons_false_prop = list_tests::any_cons_false_source_theorem();
    let any_computes_to_bool_prop = list_tests::any_computes_to_bool_source_theorem();
    let any_append_prop = list_tests::any_append_source_theorem();
    let all_true_implies_not_any_false_prop =
        list_tests::all_true_implies_not_any_false_source_theorem();
    let any_true_implies_not_all_false_prop =
        list_tests::any_true_implies_not_all_false_source_theorem();
    let find_nil_prop = list_tests::find_nil_source_theorem();
    let find_cons_true_prop = list_tests::find_cons_true_source_theorem();
    let find_cons_false_prop = list_tests::find_cons_false_source_theorem();
    let find_append_prop = list_tests::find_append_source_theorem();
    let elem_index_nil_prop = list_tests::elem_index_nil_source_theorem();
    let elem_index_cons_true_prop = list_tests::elem_index_cons_true_source_theorem();
    let elem_index_cons_false_none_prop = list_tests::elem_index_cons_false_none_source_theorem();
    let elem_index_cons_false_some_prop = list_tests::elem_index_cons_false_some_source_theorem();
    let elem_index_cons_some_cases_prop = list_tests::elem_index_cons_some_cases_source_theorem();
    let elem_index_append_left_prop = list_tests::elem_index_append_left_source_theorem();
    let elem_index_cons_none_parts_prop = list_tests::elem_index_cons_none_parts_source_theorem();
    let elem_index_append_right_prop = list_tests::elem_index_append_right_source_theorem();
    let value_eq_true_true_prop = list_tests::value_eq_true_true_source_theorem();
    let value_eq_true_false_prop = list_tests::value_eq_true_false_source_theorem();
    let value_eq_nil_prop = list_tests::value_eq_nil_source_theorem();
    let value_eq_nil_cons_prop = list_tests::value_eq_nil_cons_source_theorem();
    let value_eq_cons_nil_prop = list_tests::value_eq_cons_nil_source_theorem();
    let value_eq_cons_prop = list_tests::value_eq_cons_source_theorem();
    let value_kind_symbol_implies_is_symbol_prop =
        list_tests::value_kind_symbol_implies_is_symbol_source_theorem();
    let value_kind_lambda_implies_is_lambda_prop =
        list_tests::value_kind_lambda_implies_is_lambda_source_theorem();
    let is_symbol_true_implies_is_lambda_false_prop =
        list_tests::is_symbol_true_implies_is_lambda_false_source_theorem();
    let is_symbol_true_implies_is_list_value_false_prop =
        list_tests::is_symbol_true_implies_is_list_value_false_source_theorem();
    let is_lambda_true_implies_is_symbol_false_prop =
        list_tests::is_lambda_true_implies_is_symbol_false_source_theorem();
    let is_lambda_true_implies_is_list_value_false_prop =
        list_tests::is_lambda_true_implies_is_list_value_false_source_theorem();
    let is_list_value_true_implies_is_symbol_false_prop =
        list_tests::is_list_value_true_implies_is_symbol_false_source_theorem();
    let is_list_value_true_implies_is_lambda_false_prop =
        list_tests::is_list_value_true_implies_is_lambda_false_source_theorem();
    let value_kind_exactly_one_prop = list_tests::value_kind_exactly_one_source_theorem();
    let value_eq_comparable_symbol_prop = list_tests::value_eq_comparable_symbol_source_theorem();
    let value_eq_comparable_nil_prop = list_tests::value_eq_comparable_nil_source_theorem();
    let value_eq_comparable_cons_prop = list_tests::value_eq_comparable_cons_source_theorem();
    let value_eq_comparable_no_lambdas_prop =
        list_tests::value_eq_comparable_no_lambdas_source_theorem();
    let value_eq_true_implies_not_lambdas_prop =
        list_tests::value_eq_true_implies_not_lambdas_source_theorem();
    let value_non_symbol_non_lambda_non_bv32_is_list_prop =
        list_tests::value_non_symbol_non_lambda_non_bv32_is_list_source_theorem();
    let value_eq_left_non_symbol_true_implies_lists_prop =
        list_tests::value_eq_left_non_symbol_true_implies_lists_source_theorem();
    let value_eq_left_symbol_true_prop = list_tests::value_eq_left_symbol_true_source_theorem();
    let value_eq_left_symbol_sound_prop = list_tests::value_eq_left_symbol_sound_source_theorem();
    let value_eq_cons_true_elim_prop = list_tests::value_eq_cons_true_elim_source_theorem();
    let value_eq_cons_false_cases_prop = list_tests::value_eq_cons_false_cases_source_theorem();
    let cons_congr_prop = list_tests::cons_congr_source_theorem();
    let value_eq_sound_prop = list_tests::value_eq_sound_source_theorem();
    let value_eq_refl_prop = list_tests::value_eq_refl_source_theorem();
    let value_eq_true_implies_comparable_left_prop =
        list_tests::value_eq_true_implies_comparable_left_source_theorem();
    let value_eq_true_implies_comparable_right_prop =
        list_tests::value_eq_true_implies_comparable_right_source_theorem();
    let value_eq_symm_prop = list_tests::value_eq_symm_source_theorem();
    let value_eq_trans_prop = list_tests::value_eq_trans_source_theorem();
    let value_eq_complete_for_comparable_values_prop =
        list_tests::value_eq_complete_for_comparable_values_source_theorem();
    let value_eq_false_implies_not_equal_for_comparable_values_prop =
        list_tests::value_eq_false_implies_not_equal_for_comparable_values_source_theorem();
    let symbol_not_list_prop = list_tests::symbol_not_list_source_theorem();
    let symbol_not_lambda_prop = list_tests::symbol_not_lambda_source_theorem();
    let list_not_lambda_prop = list_tests::list_not_lambda_source_theorem();
    let member_nil_prop = list_tests::member_nil_source_theorem();
    let member_cons_true_prop = list_tests::member_cons_true_source_theorem();
    let member_cons_false_prop = list_tests::member_cons_false_source_theorem();
    let member_computes_to_bool_prop = list_tests::member_computes_to_bool_source_theorem();
    let member_is_bool_for_comparable_value_prop =
        list_tests::member_is_bool_for_comparable_value_source_theorem();
    let member_cons_or_prop = list_tests::member_cons_or_source_theorem();
    let member_append_prop = list_tests::member_append_source_theorem();
    let all_nil_prop = list_tests::all_nil_source_theorem();
    let all_cons_true_prop = list_tests::all_cons_true_source_theorem();
    let all_cons_false_prop = list_tests::all_cons_false_source_theorem();
    let all_computes_to_bool_prop = list_tests::all_computes_to_bool_source_theorem();
    let all_cons_true_parts_prop = list_tests::all_cons_true_parts_source_theorem();
    let all_append_prop = list_tests::all_append_source_theorem();
    let map_identity_prop = list_tests::map_identity_source_theorem();
    let map_compose_prop = list_tests::map_compose_source_theorem();
    let map_congr_prop = list_tests::map_congr_source_theorem();
    let map_append_prop = list_tests::map_append_source_theorem();
    let map_snoc_prop = list_tests::map_snoc_source_theorem();
    let map_take_prop = list_tests::map_take_source_theorem();
    let map_drop_prop = list_tests::map_drop_source_theorem();
    let option_map_nth_prop = list_tests::option_map_nth_source_theorem();
    let option_map_find_prop = list_tests::option_map_find_source_theorem();
    let option_bind_find_none_prop = list_tests::option_bind_find_none_source_theorem();
    let option_bind_find_some_prop = list_tests::option_bind_find_some_source_theorem();
    let concat_map_singleton_prop = list_tests::concat_map_singleton_source_theorem();
    let concat_map_append_prop = list_tests::concat_map_append_source_theorem();
    let concat_map_as_concat_map_prop = list_tests::concat_map_as_concat_map_source_theorem();
    let fold_right_cons_nil_prop = list_tests::fold_right_cons_nil_source_theorem();
    let fold_right_append_prop = list_tests::fold_right_append_source_theorem();
    let fold_left_append_prop = list_tests::fold_left_append_source_theorem();
    let fold_right_map_prop = list_tests::fold_right_map_source_theorem();
    let fold_left_map_prop = list_tests::fold_left_map_source_theorem();
    let fold_left_reverse_acc_prop = list_tests::fold_left_reverse_acc_source_theorem();
    let fold_left_reverse_prop = list_tests::fold_left_reverse_source_theorem();
    let last_nil_errors_prop = list_tests::last_nil_errors_source_theorem();
    let last_singleton_prop = list_tests::last_singleton_source_theorem();
    let last_cons_prop = list_tests::last_cons_source_theorem();
    let init_nil_errors_prop = list_tests::init_nil_errors_source_theorem();
    let init_singleton_prop = list_tests::init_singleton_source_theorem();
    let init_cons_prop = list_tests::init_cons_source_theorem();
    let null_nil_prop = list_tests::null_nil_source_theorem();
    let null_cons_prop = list_tests::null_cons_source_theorem();
    let is_singleton_nil_prop = list_tests::is_singleton_nil_source_theorem();
    let is_singleton_singleton_prop = list_tests::is_singleton_singleton_source_theorem();
    let is_singleton_cons_prop = list_tests::is_singleton_cons_source_theorem();
    let is_pair_nil_false_prop = list_tests::is_pair_nil_false_source_theorem();
    let is_pair_singleton_false_prop = list_tests::is_pair_singleton_false_source_theorem();
    let is_pair_cons_cons_nil_true_prop = list_tests::is_pair_cons_cons_nil_true_source_theorem();
    let is_pair_cons_cons_cons_false_prop =
        list_tests::is_pair_cons_cons_cons_false_source_theorem();
    let is_pair_cons_cons_true_elim_prop = list_tests::is_pair_cons_cons_true_elim_source_theorem();
    let is_pair_cons_true_elim_prop = list_tests::is_pair_cons_true_elim_source_theorem();
    let is_pair_true_elim_prop = list_tests::is_pair_true_elim_source_theorem();
    let all_is_pair_cons_true_parts_prop = list_tests::all_is_pair_cons_true_parts_source_theorem();
    let append_nil_prop = list_tests::append_nil_computes_to_list_source_theorem();
    let append_prop = list_tests::append_computes_to_list_source_theorem();
    let append_nil_returns_right_prop = list_tests::append_nil_returns_right_source_theorem();
    let append_right_nil_prop = list_tests::append_right_nil_source_theorem();
    let append_cons_prop = list_tests::append_cons_source_theorem();
    let append_singleton_prop = list_tests::append_singleton_source_theorem();
    let append_congr_left_prop = list_tests::append_congr_left_source_theorem();
    let append_congr_right_prop = list_tests::append_congr_right_source_theorem();
    let append_congr_prop = list_tests::append_congr_source_theorem();
    let append_assoc_prop = list_tests::append_assoc_source_theorem();

    assert_eq!(
        theory.theorem(theorem("nil_is_list")),
        Some(&nil_is_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("cons_is_list")),
        Some(&cons_is_list_prop)
    );
    assert_eq!(theory.theorem(theorem("cons_head")), Some(&cons_head_prop));
    assert_eq!(theory.theorem(theorem("cons_tail")), Some(&cons_tail_prop));
    assert_eq!(
        theory.theorem(theorem("nil_not_cons")),
        Some(&nil_not_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("cons_not_nil")),
        Some(&cons_not_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("cons_injective_head")),
        Some(&cons_injective_head_prop)
    );
    assert_eq!(
        theory.theorem(theorem("cons_injective_tail")),
        Some(&cons_injective_tail_prop)
    );
    assert_eq!(
        theory.theorem(theorem("cons_injective")),
        Some(&cons_injective_prop)
    );
    assert_eq!(theory.theorem(theorem("list_eta")), Some(&list_eta_prop));
    assert_eq!(
        theory.theorem(theorem("reverse_acc_computes_to_list")),
        Some(&reverse_acc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_computes_to_list")),
        Some(&reverse_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_nil_computes_to_list")),
        Some(&reverse_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_nil")),
        Some(&reverse_nil_exact_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_singleton")),
        Some(&reverse_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_congr")),
        Some(&reverse_congr_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_acc_append")),
        Some(&reverse_acc_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_cons")),
        Some(&reverse_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_acc_reverse")),
        Some(&reverse_acc_reverse_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_double")),
        Some(&reverse_double_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_acc_of_append")),
        Some(&reverse_acc_of_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_append")),
        Some(&reverse_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("map_reverse")),
        Some(&map_reverse_prop)
    );
    assert_eq!(
        theory.theorem(theorem("snoc_computes_to_list")),
        Some(&snoc_prop)
    );
    assert_eq!(theory.theorem(theorem("snoc_nil")), Some(&snoc_nil_prop));
    assert_eq!(theory.theorem(theorem("snoc_cons")), Some(&snoc_cons_prop));
    assert_eq!(
        theory.theorem(theorem("member_snoc")),
        Some(&member_snoc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("tail_snoc_after_snoc")),
        Some(&tail_snoc_after_snoc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_lists_snoc")),
        Some(&all_lists_snoc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_nil")),
        Some(&concat_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_cons")),
        Some(&concat_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_computes_to_list")),
        Some(&concat_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_append")),
        Some(&concat_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("map_length_nil")),
        Some(&map_length_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("map_length_cons")),
        Some(&map_length_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("map_length_computes_to_list")),
        Some(&map_length_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_concat")),
        Some(&length_concat_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_nil")),
        Some(&length_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_cons")),
        Some(&length_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_singleton")),
        Some(&length_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_computes_to_list")),
        Some(&length_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_append")),
        Some(&length_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_length_singleton")),
        Some(&append_length_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_snoc")),
        Some(&length_snoc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_take")),
        Some(&length_take_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_drop")),
        Some(&length_drop_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_take_add_length_drop")),
        Some(&length_take_add_length_drop_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_reverse")),
        Some(&length_reverse_prop)
    );
    assert_eq!(theory.theorem(theorem("take_zero")), Some(&take_zero_prop));
    assert_eq!(theory.theorem(theorem("take_nil")), Some(&take_nil_prop));
    assert_eq!(theory.theorem(theorem("take_cons")), Some(&take_cons_prop));
    assert_eq!(
        theory.theorem(theorem("take_computes_to_list")),
        Some(&take_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("take_congr_count_computation")),
        Some(&take_congr_count_computation_prop)
    );
    assert_eq!(
        theory.theorem(theorem("take_congr_list_computation")),
        Some(&take_congr_list_computation_prop)
    );
    assert_eq!(theory.theorem(theorem("drop_zero")), Some(&drop_zero_prop));
    assert_eq!(theory.theorem(theorem("drop_nil")), Some(&drop_nil_prop));
    assert_eq!(theory.theorem(theorem("drop_cons")), Some(&drop_cons_prop));
    assert_eq!(
        theory.theorem(theorem("drop_computes_to_list")),
        Some(&drop_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("drop_congr_count_computation")),
        Some(&drop_congr_count_computation_prop)
    );
    assert_eq!(
        theory.theorem(theorem("drop_congr_list_computation")),
        Some(&drop_congr_list_computation_prop)
    );
    assert_eq!(theory.theorem(theorem("take_take")), Some(&take_take_prop));
    assert_eq!(theory.theorem(theorem("drop_drop")), Some(&drop_drop_prop));
    assert_eq!(
        theory.theorem(theorem("take_drop_commute")),
        Some(&take_drop_commute_prop)
    );
    assert_eq!(
        theory.theorem(theorem("split_at_def")),
        Some(&split_at_def_prop)
    );
    assert_eq!(
        theory.theorem(theorem("split_at_zero")),
        Some(&split_at_zero_prop)
    );
    assert_eq!(
        theory.theorem(theorem("split_at_nil")),
        Some(&split_at_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("split_at_cons")),
        Some(&split_at_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("split_at_computes_to_pair")),
        Some(&split_at_computes_to_pair_prop)
    );
    assert_eq!(
        theory.theorem(theorem("split_at_first_take")),
        Some(&split_at_first_take_prop)
    );
    assert_eq!(
        theory.theorem(theorem("split_at_second_drop")),
        Some(&split_at_second_drop_prop)
    );
    assert_eq!(
        theory.theorem(theorem("nth_zero_nil")),
        Some(&nth_zero_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("nth_zero_cons")),
        Some(&nth_zero_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("nth_cons_nil")),
        Some(&nth_cons_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("nth_cons_cons")),
        Some(&nth_cons_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("nth_zero_cons_some")),
        Some(&nth_zero_cons_some_prop)
    );
    assert_eq!(
        theory.theorem(theorem("nth_out_of_bounds_none")),
        Some(&nth_out_of_bounds_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("nth_computes_to_option")),
        Some(&nth_computes_to_option_prop)
    );
    assert_eq!(
        theory.theorem(theorem("replicate_zero")),
        Some(&replicate_zero_prop)
    );
    assert_eq!(
        theory.theorem(theorem("replicate_cons")),
        Some(&replicate_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("replicate_computes_to_list")),
        Some(&replicate_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_replicate")),
        Some(&length_replicate_prop)
    );
    assert_eq!(
        theory.theorem(theorem("take_replicate")),
        Some(&take_replicate_prop)
    );
    assert_eq!(
        theory.theorem(theorem("drop_replicate")),
        Some(&drop_replicate_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intersperse_nil")),
        Some(&intersperse_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intersperse_singleton")),
        Some(&intersperse_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intersperse_cons_cons")),
        Some(&intersperse_cons_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intersperse_cons_computes_to_list")),
        Some(&intersperse_cons_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intersperse_computes_to_list")),
        Some(&intersperse_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intercalate_nil")),
        Some(&intercalate_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intercalate_singleton")),
        Some(&intercalate_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intercalate_cons_cons")),
        Some(&intercalate_cons_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_list_value_true_implies_is_list")),
        Some(&is_list_value_true_implies_is_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_kind_list_implies_is_list")),
        Some(&value_kind_list_implies_is_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_list_implies_is_list_value_true")),
        Some(&is_list_implies_is_list_value_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_lists_cons")),
        Some(&all_lists_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_lists_cons_true")),
        Some(&all_lists_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("symbol_eq_true_implies_is_symbol_left")),
        Some(&symbol_eq_true_implies_is_symbol_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("symbol_eq_true_implies_is_symbol_right")),
        Some(&symbol_eq_true_implies_is_symbol_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("symbol_eq_false_distinct")),
        Some(&symbol_eq_false_distinct_prop)
    );
    assert_eq!(
        theory.theorem(theorem("symbol_eq_symm")),
        Some(&symbol_eq_symm_prop)
    );
    assert_eq!(
        theory.theorem(theorem("symbol_eq_refl")),
        Some(&symbol_eq_refl_prop)
    );
    assert_eq!(
        theory.theorem(theorem("symbol_eq_computes_to_bool")),
        Some(&symbol_eq_computes_to_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_false_result_with_true_else")),
        Some(&if_false_result_with_true_else_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_false_result_with_error_else")),
        Some(&if_false_result_with_error_else_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_false_result_with_false_else")),
        Some(&if_false_result_with_false_else_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_true_result_with_true_then")),
        Some(&if_true_result_with_true_then_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_true_result_with_true_else")),
        Some(&if_true_result_with_true_else_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_false_result_with_false_then")),
        Some(&if_false_result_with_false_then_prop)
    );
    assert_eq!(
        theory.theorem(theorem("true_is_bool")),
        Some(&true_is_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("false_is_bool")),
        Some(&false_is_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_bool_elim")),
        Some(&is_bool_elim_prop)
    );
    assert_eq!(
        theory.theorem(theorem("bool_distinct")),
        Some(&bool_distinct_prop)
    );
    assert_eq!(theory.theorem(theorem("not_congr")), Some(&not_congr_prop));
    assert_eq!(
        theory.theorem(theorem("and_congr_left")),
        Some(&and_congr_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_congr_right")),
        Some(&and_congr_right_prop)
    );
    assert_eq!(theory.theorem(theorem("and_congr")), Some(&and_congr_prop));
    assert_eq!(
        theory.theorem(theorem("or_congr_left")),
        Some(&or_congr_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_congr_right")),
        Some(&or_congr_right_prop)
    );
    assert_eq!(theory.theorem(theorem("or_congr")), Some(&or_congr_prop));
    assert_eq!(
        theory.theorem(theorem("not_true_elim")),
        Some(&not_true_elim_prop)
    );
    assert_eq!(
        theory.theorem(theorem("not_false_elim")),
        Some(&not_false_elim_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_computes_to_bool")),
        Some(&if_computes_to_bool_prop)
    );
    assert_eq!(theory.theorem(theorem("if_same")), Some(&if_same_prop));
    assert_eq!(theory.theorem(theorem("if_not")), Some(&if_not_prop));
    assert_eq!(
        theory.theorem(theorem("if_congr_condition")),
        Some(&if_congr_condition_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_congr_then")),
        Some(&if_congr_then_prop)
    );
    assert_eq!(
        theory.theorem(theorem("if_congr_else")),
        Some(&if_congr_else_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_true_intro")),
        Some(&and_true_intro_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_true_elim_left")),
        Some(&and_true_elim_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_true_elim_right")),
        Some(&and_true_elim_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_false_cases")),
        Some(&and_false_cases_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_false_intro")),
        Some(&or_false_intro_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_false_elim_left")),
        Some(&or_false_elim_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_false_elim_right")),
        Some(&or_false_elim_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_true_cases")),
        Some(&or_true_cases_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_prop_to_bool")),
        Some(&and_prop_to_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_bool_to_prop")),
        Some(&and_bool_to_prop_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_prop_to_bool_left")),
        Some(&or_prop_to_bool_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_prop_to_bool_right")),
        Some(&or_prop_to_bool_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_bool_to_prop")),
        Some(&or_bool_to_prop_prop)
    );
    assert_eq!(
        theory.theorem(theorem("not_bool_to_absurd")),
        Some(&not_bool_to_absurd_prop)
    );
    assert_eq!(
        theory.theorem(theorem("not_absurd_to_bool_false")),
        Some(&not_absurd_to_bool_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_absorb_or")),
        Some(&and_absorb_or_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_absorb_and")),
        Some(&or_absorb_and_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_distrib_or_left")),
        Some(&and_distrib_or_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("and_distrib_or_right")),
        Some(&and_distrib_or_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_distrib_and_left")),
        Some(&or_distrib_and_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("or_distrib_and_right")),
        Some(&or_distrib_and_right_prop)
    );
    assert_eq!(theory.theorem(theorem("not_and")), Some(&not_and_prop));
    assert_eq!(theory.theorem(theorem("not_or")), Some(&not_or_prop));
    assert_eq!(
        theory.theorem(theorem("none_is_none")),
        Some(&none_is_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("some_is_none")),
        Some(&some_is_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("none_is_some")),
        Some(&none_is_some_prop)
    );
    assert_eq!(
        theory.theorem(theorem("some_is_some")),
        Some(&some_is_some_prop)
    );
    assert_eq!(
        theory.theorem(theorem("some_congr")),
        Some(&some_congr_prop)
    );
    assert_eq!(
        theory.theorem(theorem("some_injective")),
        Some(&some_injective_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_none")),
        Some(&option_map_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_some")),
        Some(&option_map_some_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_none")),
        Some(&option_bind_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_some")),
        Some(&option_bind_some_prop)
    );
    assert_eq!(
        theory.theorem(theorem("unwrap_or_none")),
        Some(&unwrap_or_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("unwrap_or_some")),
        Some(&unwrap_or_some_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_filter_none")),
        Some(&option_filter_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_filter_some_true")),
        Some(&option_filter_some_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_filter_some_false")),
        Some(&option_filter_some_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_computes_to_option")),
        Some(&option_map_computes_to_option_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_computes_to_option")),
        Some(&option_bind_computes_to_option_prop)
    );
    assert_eq!(
        theory.theorem(theorem("unwrap_or_computes_to_value")),
        Some(&unwrap_or_computes_to_value_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_filter_computes_to_option")),
        Some(&option_filter_computes_to_option_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_identity")),
        Some(&option_map_identity_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_compose")),
        Some(&option_map_compose_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_left_identity")),
        Some(&option_bind_left_identity_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_right_identity")),
        Some(&option_bind_right_identity_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_assoc")),
        Some(&option_bind_assoc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_congr_function")),
        Some(&option_map_congr_function_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_congr_option")),
        Some(&option_map_congr_option_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_congr_option_computation")),
        Some(&option_map_congr_option_computation_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_congr")),
        Some(&option_map_congr_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_congr_function")),
        Some(&option_bind_congr_function_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_congr_option")),
        Some(&option_bind_congr_option_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_congr_option_computation")),
        Some(&option_bind_congr_option_computation_prop)
    );
    assert_eq!(
        theory.theorem(theorem("unwrap_or_congr_default")),
        Some(&unwrap_or_congr_default_prop)
    );
    assert_eq!(
        theory.theorem(theorem("unwrap_or_congr_option")),
        Some(&unwrap_or_congr_option_prop)
    );
    assert_eq!(
        theory.theorem(theorem("pair_first")),
        Some(&pair_first_prop)
    );
    assert_eq!(theory.theorem(theorem("pair_tail")), Some(&pair_tail_prop));
    assert_eq!(
        theory.theorem(theorem("pair_second")),
        Some(&pair_second_prop)
    );
    assert_eq!(
        theory.theorem(theorem("pair_computes_to_list")),
        Some(&pair_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("pair_computes_to_value")),
        Some(&pair_computes_to_value_prop)
    );
    assert_eq!(theory.theorem(theorem("pair_eta")), Some(&pair_eta_prop));
    assert_eq!(
        theory.theorem(theorem("pair_congr")),
        Some(&pair_congr_prop)
    );
    assert_eq!(
        theory.theorem(theorem("pair_first_from_computation")),
        Some(&pair_first_from_computation_prop)
    );
    assert_eq!(
        theory.theorem(theorem("pair_second_from_computation")),
        Some(&pair_second_from_computation_prop)
    );
    assert_eq!(
        theory.theorem(theorem("pair_injective_first")),
        Some(&pair_injective_first_prop)
    );
    assert_eq!(
        theory.theorem(theorem("pair_injective_second")),
        Some(&pair_injective_second_prop)
    );
    assert_eq!(
        theory.theorem(theorem("pair_injective")),
        Some(&pair_injective_prop)
    );
    assert_eq!(
        theory.theorem(theorem("list_pair_first_from_computation")),
        Some(&list_pair_first_from_computation_prop)
    );
    assert_eq!(
        theory.theorem(theorem("list_pair_second_from_computation")),
        Some(&list_pair_second_from_computation_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intercalate_cons_computes_to_list")),
        Some(&intercalate_cons_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("intercalate_computes_to_list")),
        Some(&intercalate_computes_to_list_prop)
    );
    assert_eq!(theory.theorem(theorem("map_nil")), Some(&map_nil_prop));
    assert_eq!(theory.theorem(theorem("map_cons")), Some(&map_cons_prop));
    assert_eq!(
        theory.theorem(theorem("map_computes_to_list")),
        Some(&map_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("length_map")),
        Some(&length_map_prop)
    );
    assert_eq!(
        theory.theorem(theorem("map_replicate")),
        Some(&map_replicate_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_nil")),
        Some(&concat_map_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_cons")),
        Some(&concat_map_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_computes_to_list")),
        Some(&concat_map_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_nil")),
        Some(&fold_right_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_cons")),
        Some(&fold_right_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_computes_to_value")),
        Some(&fold_right_computes_to_value_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_congr")),
        Some(&fold_right_congr_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_nil")),
        Some(&fold_left_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_cons")),
        Some(&fold_left_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_computes_to_value")),
        Some(&fold_left_computes_to_value_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_congr")),
        Some(&fold_left_congr_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_left_nil")),
        Some(&zip_left_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_right_nil")),
        Some(&zip_right_nil_prop)
    );
    assert_eq!(theory.theorem(theorem("zip_cons")), Some(&zip_cons_prop));
    assert_eq!(
        theory.theorem(theorem("zip_computes_to_list")),
        Some(&zip_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_pair_shape")),
        Some(&zip_pair_shape_prop)
    );
    assert_eq!(theory.theorem(theorem("unzip_nil")), Some(&unzip_nil_prop));
    assert_eq!(
        theory.theorem(theorem("unzip_cons")),
        Some(&unzip_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("unzip_pair_shape")),
        Some(&unzip_pair_shape_prop)
    );
    assert_eq!(theory.theorem(theorem("zip_unzip")), Some(&zip_unzip_prop));
    assert_eq!(theory.theorem(theorem("unzip_zip")), Some(&unzip_zip_prop));
    assert_eq!(
        theory.theorem(theorem("zip_with_as_map_zip")),
        Some(&zip_with_as_map_zip_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_with_left_nil")),
        Some(&zip_with_left_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_with_right_nil")),
        Some(&zip_with_right_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_with_cons")),
        Some(&zip_with_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_with_computes_to_list")),
        Some(&zip_with_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_nil")),
        Some(&filter_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_cons_true")),
        Some(&filter_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_cons_false")),
        Some(&filter_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_computes_to_list")),
        Some(&filter_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_congr")),
        Some(&filter_congr_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reject_nil")),
        Some(&reject_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reject_cons_true")),
        Some(&reject_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reject_cons_false")),
        Some(&reject_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reject_computes_to_list")),
        Some(&reject_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_append")),
        Some(&filter_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reject_append")),
        Some(&reject_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_idempotent")),
        Some(&filter_idempotent_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reject_idempotent")),
        Some(&reject_idempotent_prop)
    );
    assert_eq!(
        theory.theorem(theorem("partition_nil")),
        Some(&partition_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("partition_cons_true")),
        Some(&partition_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("partition_cons_false")),
        Some(&partition_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("partition_computes_to_pair")),
        Some(&partition_computes_to_pair_prop)
    );
    assert_eq!(
        theory.theorem(theorem("partition_first_filter")),
        Some(&partition_first_filter_prop)
    );
    assert_eq!(
        theory.theorem(theorem("partition_second_filter_false")),
        Some(&partition_second_filter_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("partition_second_reject")),
        Some(&partition_second_reject_prop)
    );
    assert_eq!(theory.theorem(theorem("any_nil")), Some(&any_nil_prop));
    assert_eq!(
        theory.theorem(theorem("any_cons_true")),
        Some(&any_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("any_cons_false")),
        Some(&any_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("any_computes_to_bool")),
        Some(&any_computes_to_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("any_append")),
        Some(&any_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_true_implies_not_any_false")),
        Some(&all_true_implies_not_any_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("any_true_implies_not_all_false")),
        Some(&any_true_implies_not_all_false_prop)
    );
    assert_eq!(theory.theorem(theorem("find_nil")), Some(&find_nil_prop));
    assert_eq!(
        theory.theorem(theorem("find_cons_true")),
        Some(&find_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("find_cons_false")),
        Some(&find_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("find_append")),
        Some(&find_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("elem_index_nil")),
        Some(&elem_index_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("elem_index_cons_true")),
        Some(&elem_index_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("elem_index_cons_false_none")),
        Some(&elem_index_cons_false_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("elem_index_cons_false_some")),
        Some(&elem_index_cons_false_some_prop)
    );
    assert_eq!(
        theory.theorem(theorem("elem_index_cons_some_cases")),
        Some(&elem_index_cons_some_cases_prop)
    );
    assert_eq!(
        theory.theorem(theorem("elem_index_append_left")),
        Some(&elem_index_append_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("elem_index_cons_none_parts")),
        Some(&elem_index_cons_none_parts_prop)
    );
    assert_eq!(
        theory.theorem(theorem("elem_index_append_right")),
        Some(&elem_index_append_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_true_true")),
        Some(&value_eq_true_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_true_false")),
        Some(&value_eq_true_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_nil")),
        Some(&value_eq_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_nil_cons")),
        Some(&value_eq_nil_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_cons_nil")),
        Some(&value_eq_cons_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_cons")),
        Some(&value_eq_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_nil")),
        Some(&member_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_cons_true")),
        Some(&member_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_cons_false")),
        Some(&member_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_computes_to_bool")),
        Some(&member_computes_to_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_is_bool_for_comparable_value")),
        Some(&member_is_bool_for_comparable_value_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_cons_or")),
        Some(&member_cons_or_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_append")),
        Some(&member_append_prop)
    );
    assert_eq!(theory.theorem(theorem("all_nil")), Some(&all_nil_prop));
    assert_eq!(
        theory.theorem(theorem("all_cons_true")),
        Some(&all_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_cons_false")),
        Some(&all_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_computes_to_bool")),
        Some(&all_computes_to_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_cons_true_parts")),
        Some(&all_cons_true_parts_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_append")),
        Some(&all_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("map_identity")),
        Some(&map_identity_prop)
    );
    assert_eq!(
        theory.theorem(theorem("map_compose")),
        Some(&map_compose_prop)
    );
    assert_eq!(theory.theorem(theorem("map_congr")), Some(&map_congr_prop));
    assert_eq!(
        theory.theorem(theorem("map_append")),
        Some(&map_append_prop)
    );
    assert_eq!(theory.theorem(theorem("map_snoc")), Some(&map_snoc_prop));
    assert_eq!(theory.theorem(theorem("map_take")), Some(&map_take_prop));
    assert_eq!(theory.theorem(theorem("map_drop")), Some(&map_drop_prop));
    assert_eq!(
        theory.theorem(theorem("option_map_nth")),
        Some(&option_map_nth_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_map_find")),
        Some(&option_map_find_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_find_none")),
        Some(&option_bind_find_none_prop)
    );
    assert_eq!(
        theory.theorem(theorem("option_bind_find_some")),
        Some(&option_bind_find_some_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_singleton")),
        Some(&concat_map_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_append")),
        Some(&concat_map_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_as_concat_map")),
        Some(&concat_map_as_concat_map_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_cons_nil")),
        Some(&fold_right_cons_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_append")),
        Some(&fold_right_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_append")),
        Some(&fold_left_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_map")),
        Some(&fold_right_map_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_map")),
        Some(&fold_left_map_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_reverse_acc")),
        Some(&fold_left_reverse_acc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_reverse")),
        Some(&fold_left_reverse_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_take_drop")),
        Some(&append_take_drop_prop)
    );
    assert_eq!(
        theory.theorem(theorem("last_nil_errors")),
        Some(&last_nil_errors_prop)
    );
    assert_eq!(
        theory.theorem(theorem("last_singleton")),
        Some(&last_singleton_prop)
    );
    assert_eq!(theory.theorem(theorem("last_cons")), Some(&last_cons_prop));
    assert_eq!(
        theory.theorem(theorem("init_nil_errors")),
        Some(&init_nil_errors_prop)
    );
    assert_eq!(
        theory.theorem(theorem("init_singleton")),
        Some(&init_singleton_prop)
    );
    assert_eq!(theory.theorem(theorem("init_cons")), Some(&init_cons_prop));
    assert_eq!(theory.theorem(theorem("null_nil")), Some(&null_nil_prop));
    assert_eq!(theory.theorem(theorem("null_cons")), Some(&null_cons_prop));
    assert_eq!(
        theory.theorem(theorem("is_singleton_nil")),
        Some(&is_singleton_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_singleton_singleton")),
        Some(&is_singleton_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_singleton_cons")),
        Some(&is_singleton_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_pair_nil_false")),
        Some(&is_pair_nil_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_pair_singleton_false")),
        Some(&is_pair_singleton_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_pair_cons_cons_nil_true")),
        Some(&is_pair_cons_cons_nil_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_pair_cons_cons_cons_false")),
        Some(&is_pair_cons_cons_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_pair_cons_cons_true_elim")),
        Some(&is_pair_cons_cons_true_elim_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_pair_cons_true_elim")),
        Some(&is_pair_cons_true_elim_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_pair_true_elim")),
        Some(&is_pair_true_elim_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_is_pair_cons_true_parts")),
        Some(&all_is_pair_cons_true_parts_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_nil_computes_to_list")),
        Some(&append_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_computes_to_list")),
        Some(&append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_nil_returns_right")),
        Some(&append_nil_returns_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_right_nil")),
        Some(&append_right_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_cons")),
        Some(&append_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_singleton")),
        Some(&append_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_congr_left")),
        Some(&append_congr_left_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_congr_right")),
        Some(&append_congr_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_congr")),
        Some(&append_congr_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_assoc")),
        Some(&append_assoc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_take_drop")),
        Some(&append_take_drop_prop)
    );
    assert_eq!(
        theory
            .known(theorem("reverse_computes_to_list"))
            .expect("reverse theorem should be defined")
            .prop(),
        &reverse_prop,
    );
    assert_eq!(
        checked_theorem("reverse_computes_to_list")
            .expect("reverse theorem source proof should check with dependencies")
            .prop(),
        &reverse_prop,
    );
    assert_eq!(
        checked_theorem("reverse_nil_computes_to_list")
            .expect("reverse nil theorem source proof should check with dependencies")
            .prop(),
        &reverse_nil_prop,
    );
    assert_eq!(
        checked_theorem("reverse_nil")
            .expect("reverse nil exact theorem source proof should check with dependencies")
            .prop(),
        &reverse_nil_exact_prop,
    );
    assert_eq!(
        checked_theorem("reverse_singleton")
            .expect("reverse singleton theorem source proof should check with dependencies")
            .prop(),
        &reverse_singleton_prop,
    );
    assert_eq!(
        checked_theorem("reverse_congr")
            .expect("reverse congruence theorem source proof should check with dependencies")
            .prop(),
        &reverse_congr_prop,
    );
    assert_eq!(
        checked_theorem("reverse_acc_append")
            .expect("reverse accumulator theorem source proof should check with dependencies")
            .prop(),
        &reverse_acc_append_prop,
    );
    assert_eq!(
        checked_theorem("reverse_cons")
            .expect("reverse cons theorem source proof should check with dependencies")
            .prop(),
        &reverse_cons_prop,
    );
    assert_eq!(
        checked_theorem("reverse_acc_reverse")
            .expect(
                "reverse accumulator inverse theorem source proof should check with dependencies"
            )
            .prop(),
        &reverse_acc_reverse_prop,
    );
    assert_eq!(
        checked_theorem("reverse_double")
            .expect("reverse double theorem source proof should check with dependencies")
            .prop(),
        &reverse_double_prop,
    );
    assert_eq!(
        checked_theorem("reverse_acc_of_append")
            .expect(
                "reverse accumulator append theorem source proof should check with dependencies"
            )
            .prop(),
        &reverse_acc_of_append_prop,
    );
    assert_eq!(
        checked_theorem("reverse_append")
            .expect("reverse append theorem source proof should check with dependencies")
            .prop(),
        &reverse_append_prop,
    );
    assert_eq!(
        checked_theorem("length_reverse")
            .expect("length reverse theorem source proof should check with dependencies")
            .prop(),
        &length_reverse_prop,
    );
    assert_eq!(
        checked_theorem("map_reverse")
            .expect("map reverse theorem source proof should check with dependencies")
            .prop(),
        &map_reverse_prop,
    );
    assert_eq!(
        checked_theorem("snoc_computes_to_list")
            .expect("snoc theorem source proof should check with dependencies")
            .prop(),
        &snoc_prop,
    );
    assert_eq!(
        checked_theorem("snoc_nil")
            .expect("snoc nil theorem source proof should check with dependencies")
            .prop(),
        &snoc_nil_prop,
    );
    assert_eq!(
        checked_theorem("snoc_cons")
            .expect("snoc cons theorem source proof should check with dependencies")
            .prop(),
        &snoc_cons_prop,
    );
    assert_eq!(
        checked_theorem("member_snoc")
            .expect("member snoc theorem source proof should check with dependencies")
            .prop(),
        &member_snoc_prop,
    );
    assert_eq!(
        checked_theorem("tail_snoc_after_snoc")
            .expect("tail snoc after snoc theorem source proof should check with dependencies")
            .prop(),
        &tail_snoc_after_snoc_prop,
    );
    assert_eq!(
        checked_theorem("concat_nil")
            .expect("concat nil theorem source proof should check with dependencies")
            .prop(),
        &concat_nil_prop,
    );
    assert_eq!(
        checked_theorem("concat_append")
            .expect("concat append theorem source proof should check with dependencies")
            .prop(),
        &concat_append_prop,
    );
    assert_eq!(
        checked_theorem("map_length_nil")
            .expect("map length nil theorem source proof should check with dependencies")
            .prop(),
        &map_length_nil_prop,
    );
    assert_eq!(
        checked_theorem("map_length_cons")
            .expect("map length cons theorem source proof should check with dependencies")
            .prop(),
        &map_length_cons_prop,
    );
    assert_eq!(
        checked_theorem("map_length_computes_to_list")
            .expect("map length computes theorem source proof should check with dependencies")
            .prop(),
        &map_length_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("length_concat")
            .expect("length concat theorem source proof should check with dependencies")
            .prop(),
        &length_concat_prop,
    );
    assert_eq!(
        checked_theorem("last_nil_errors")
            .expect("last nil theorem source proof should check with dependencies")
            .prop(),
        &last_nil_errors_prop,
    );
    assert_eq!(
        checked_theorem("last_singleton")
            .expect("last singleton theorem source proof should check with dependencies")
            .prop(),
        &last_singleton_prop,
    );
    assert_eq!(
        checked_theorem("last_cons")
            .expect("last cons theorem source proof should check with dependencies")
            .prop(),
        &last_cons_prop,
    );
    assert_eq!(
        checked_theorem("init_nil_errors")
            .expect("init nil theorem source proof should check with dependencies")
            .prop(),
        &init_nil_errors_prop,
    );
    assert_eq!(
        checked_theorem("init_singleton")
            .expect("init singleton theorem source proof should check with dependencies")
            .prop(),
        &init_singleton_prop,
    );
    assert_eq!(
        checked_theorem("init_cons")
            .expect("init cons theorem source proof should check with dependencies")
            .prop(),
        &init_cons_prop,
    );
    assert_eq!(
        checked_theorem("null_nil")
            .expect("null nil theorem source proof should check with dependencies")
            .prop(),
        &null_nil_prop,
    );
    assert_eq!(
        checked_theorem("null_cons")
            .expect("null cons theorem source proof should check with dependencies")
            .prop(),
        &null_cons_prop,
    );
    assert_eq!(
        checked_theorem("is_singleton_nil")
            .expect("is-singleton nil theorem source proof should check with dependencies")
            .prop(),
        &is_singleton_nil_prop,
    );
    assert_eq!(
        checked_theorem("is_singleton_singleton")
            .expect("is-singleton singleton theorem source proof should check with dependencies")
            .prop(),
        &is_singleton_singleton_prop,
    );
    assert_eq!(
        checked_theorem("is_singleton_cons")
            .expect("is-singleton cons theorem source proof should check with dependencies")
            .prop(),
        &is_singleton_cons_prop,
    );
    assert_eq!(
        checked_theorem("is_pair_nil_false")
            .expect("is-pair nil theorem source proof should check with dependencies")
            .prop(),
        &is_pair_nil_false_prop,
    );
    assert_eq!(
        checked_theorem("is_pair_singleton_false")
            .expect("is-pair singleton theorem source proof should check with dependencies")
            .prop(),
        &is_pair_singleton_false_prop,
    );
    assert_eq!(
        checked_theorem("is_pair_cons_cons_nil_true")
            .expect("is-pair two-element theorem source proof should check with dependencies")
            .prop(),
        &is_pair_cons_cons_nil_true_prop,
    );
    assert_eq!(
        checked_theorem("is_pair_cons_cons_cons_false")
            .expect("is-pair longer-list theorem source proof should check with dependencies")
            .prop(),
        &is_pair_cons_cons_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("is_pair_cons_cons_true_elim")
            .expect("is-pair long-list eliminator source proof should check with dependencies")
            .prop(),
        &is_pair_cons_cons_true_elim_prop,
    );
    assert_eq!(
        checked_theorem("is_pair_cons_true_elim")
            .expect("is-pair cons eliminator source proof should check with dependencies")
            .prop(),
        &is_pair_cons_true_elim_prop,
    );
    assert_eq!(
        checked_theorem("is_pair_true_elim")
            .expect("is-pair value eliminator source proof should check with dependencies")
            .prop(),
        &is_pair_true_elim_prop,
    );
    assert_eq!(
        checked_theorem("all_is_pair_cons_true_parts")
            .expect("all is-pair cons parts source proof should check with dependencies")
            .prop(),
        &all_is_pair_cons_true_parts_prop,
    );
    assert_eq!(
        checked_theorem("append_nil_computes_to_list")
            .expect("append nil theorem source proof should check with dependencies")
            .prop(),
        &append_nil_prop,
    );
    assert_eq!(
        checked_theorem("append_computes_to_list")
            .expect("append theorem source proof should check with dependencies")
            .prop(),
        &append_prop,
    );
    assert_eq!(
        checked_theorem("append_nil_returns_right")
            .expect("append nil exact theorem source proof should check with dependencies")
            .prop(),
        &append_nil_returns_right_prop,
    );
    assert_eq!(
        checked_theorem("append_right_nil")
            .expect("append right nil theorem source proof should check with dependencies")
            .prop(),
        &append_right_nil_prop,
    );
    assert_eq!(
        checked_theorem("append_cons")
            .expect("append cons theorem source proof should check with dependencies")
            .prop(),
        &append_cons_prop,
    );
    assert_eq!(
        checked_theorem("append_singleton")
            .expect("append singleton theorem source proof should check with dependencies")
            .prop(),
        &append_singleton_prop,
    );
    assert_eq!(
        checked_theorem("append_congr_left")
            .expect("append left congruence theorem source proof should check with dependencies")
            .prop(),
        &append_congr_left_prop,
    );
    assert_eq!(
        checked_theorem("append_congr_right")
            .expect("append right congruence theorem source proof should check with dependencies")
            .prop(),
        &append_congr_right_prop,
    );
    assert_eq!(
        checked_theorem("append_congr")
            .expect("append congruence theorem source proof should check with dependencies")
            .prop(),
        &append_congr_prop,
    );
    assert_eq!(
        checked_theorem("append_assoc")
            .expect("append associativity theorem source proof should check with dependencies")
            .prop(),
        &append_assoc_prop,
    );
    assert_eq!(
        checked_theorem("append_length_singleton")
            .expect("append length singleton theorem source proof should check with dependencies")
            .prop(),
        &append_length_singleton_prop,
    );
    assert_eq!(
        checked_theorem("length_snoc")
            .expect("length snoc theorem source proof should check with dependencies")
            .prop(),
        &length_snoc_prop,
    );
    assert_eq!(
        checked_theorem("length_take")
            .expect("length take theorem source proof should check with dependencies")
            .prop(),
        &length_take_prop,
    );
    assert_eq!(
        checked_theorem("length_drop")
            .expect("length drop theorem source proof should check with dependencies")
            .prop(),
        &length_drop_prop,
    );
    assert_eq!(
        checked_theorem("length_take_add_length_drop")
            .expect("length take/drop theorem source proof should check with dependencies")
            .prop(),
        &length_take_add_length_drop_prop,
    );
    assert_eq!(
        checked_theorem("take_congr_count_computation")
            .expect("take count congruence theorem source proof should check with dependencies")
            .prop(),
        &take_congr_count_computation_prop,
    );
    assert_eq!(
        checked_theorem("take_congr_list_computation")
            .expect("take list congruence theorem source proof should check with dependencies")
            .prop(),
        &take_congr_list_computation_prop,
    );
    assert_eq!(
        checked_theorem("drop_congr_count_computation")
            .expect("drop count congruence theorem source proof should check with dependencies")
            .prop(),
        &drop_congr_count_computation_prop,
    );
    assert_eq!(
        checked_theorem("drop_congr_list_computation")
            .expect("drop list congruence theorem source proof should check with dependencies")
            .prop(),
        &drop_congr_list_computation_prop,
    );
    assert_eq!(
        checked_theorem("take_take")
            .expect("take-take theorem source proof should check with dependencies")
            .prop(),
        &take_take_prop,
    );
    assert_eq!(
        checked_theorem("drop_drop")
            .expect("drop-drop theorem source proof should check with dependencies")
            .prop(),
        &drop_drop_prop,
    );
    assert_eq!(
        checked_theorem("take_drop_commute")
            .expect("take/drop commute theorem source proof should check with dependencies")
            .prop(),
        &take_drop_commute_prop,
    );
    assert_eq!(
        checked_theorem("split_at_def")
            .expect("split-at definition theorem source proof should check with dependencies")
            .prop(),
        &split_at_def_prop,
    );
    assert_eq!(
        checked_theorem("split_at_zero")
            .expect("split-at zero theorem source proof should check with dependencies")
            .prop(),
        &split_at_zero_prop,
    );
    assert_eq!(
        checked_theorem("split_at_nil")
            .expect("split-at nil theorem source proof should check with dependencies")
            .prop(),
        &split_at_nil_prop,
    );
    assert_eq!(
        checked_theorem("split_at_cons")
            .expect("split-at cons theorem source proof should check with dependencies")
            .prop(),
        &split_at_cons_prop,
    );
    assert_eq!(
        checked_theorem("split_at_computes_to_pair")
            .expect("split-at pair result theorem source proof should check with dependencies")
            .prop(),
        &split_at_computes_to_pair_prop,
    );
    assert_eq!(
        checked_theorem("split_at_first_take")
            .expect("split-at first projection theorem source proof should check with dependencies")
            .prop(),
        &split_at_first_take_prop,
    );
    assert_eq!(
        checked_theorem("split_at_second_drop")
            .expect(
                "split-at second projection theorem source proof should check with dependencies"
            )
            .prop(),
        &split_at_second_drop_prop,
    );
    assert_eq!(
        checked_theorem("nth_zero_nil")
            .expect("nth zero nil theorem source proof should check with dependencies")
            .prop(),
        &nth_zero_nil_prop,
    );
    assert_eq!(
        checked_theorem("nth_zero_cons")
            .expect("nth zero cons theorem source proof should check with dependencies")
            .prop(),
        &nth_zero_cons_prop,
    );
    assert_eq!(
        checked_theorem("nth_cons_nil")
            .expect("nth cons nil theorem source proof should check with dependencies")
            .prop(),
        &nth_cons_nil_prop,
    );
    assert_eq!(
        checked_theorem("nth_cons_cons")
            .expect("nth cons cons theorem source proof should check with dependencies")
            .prop(),
        &nth_cons_cons_prop,
    );
    assert_eq!(
        checked_theorem("nth_zero_cons_some")
            .expect("nth zero cons some theorem source proof should check with dependencies")
            .prop(),
        &nth_zero_cons_some_prop,
    );
    assert_eq!(
        checked_theorem("nth_out_of_bounds_none")
            .expect("nth out of bounds theorem source proof should check with dependencies")
            .prop(),
        &nth_out_of_bounds_none_prop,
    );
    assert_eq!(
        checked_theorem("nth_computes_to_option")
            .expect("nth option result theorem source proof should check with dependencies")
            .prop(),
        &nth_computes_to_option_prop,
    );
    assert_eq!(
        checked_theorem("symbol_eq_true_implies_is_symbol_left")
            .expect("symbol-eq left symbol theorem source proof should check with dependencies")
            .prop(),
        &symbol_eq_true_implies_is_symbol_left_prop,
    );
    assert_eq!(
        checked_theorem("symbol_eq_true_implies_is_symbol_right")
            .expect("symbol-eq right symbol theorem source proof should check with dependencies")
            .prop(),
        &symbol_eq_true_implies_is_symbol_right_prop,
    );
    assert_eq!(
        checked_theorem("symbol_eq_false_distinct")
            .expect("symbol-eq false distinct theorem source proof should check with dependencies")
            .prop(),
        &symbol_eq_false_distinct_prop,
    );
    assert_eq!(
        checked_theorem("symbol_eq_symm")
            .expect("symbol-eq symmetry theorem source proof should check with dependencies")
            .prop(),
        &symbol_eq_symm_prop,
    );
    assert_eq!(
        checked_theorem("symbol_eq_refl")
            .expect("symbol-eq reflexivity theorem source proof should check with dependencies")
            .prop(),
        &symbol_eq_refl_prop,
    );
    assert_eq!(
        checked_theorem("symbol_eq_computes_to_bool")
            .expect("symbol-eq bool result theorem source proof should check with dependencies")
            .prop(),
        &symbol_eq_computes_to_bool_prop,
    );
    assert_eq!(
        checked_theorem("if_false_result_with_true_else")
            .expect("if false result with true else theorem source proof should check")
            .prop(),
        &if_false_result_with_true_else_prop,
    );
    assert_eq!(
        checked_theorem("if_false_result_with_error_else")
            .expect("if false result with error else theorem source proof should check")
            .prop(),
        &if_false_result_with_error_else_prop,
    );
    assert_eq!(
        checked_theorem("if_false_result_with_false_else")
            .expect("if false result with false else theorem source proof should check")
            .prop(),
        &if_false_result_with_false_else_prop,
    );
    assert_eq!(
        checked_theorem("if_true_result_with_true_then")
            .expect("if true result with true then theorem source proof should check")
            .prop(),
        &if_true_result_with_true_then_prop,
    );
    assert_eq!(
        checked_theorem("if_true_result_with_true_else")
            .expect("if true result with true else theorem source proof should check")
            .prop(),
        &if_true_result_with_true_else_prop,
    );
    assert_eq!(
        checked_theorem("if_false_result_with_false_then")
            .expect("if false result with false then theorem source proof should check")
            .prop(),
        &if_false_result_with_false_then_prop,
    );
    assert_eq!(
        checked_theorem("true_is_bool")
            .expect("true bool theorem source proof should check with dependencies")
            .prop(),
        &true_is_bool_prop,
    );
    assert_eq!(
        checked_theorem("false_is_bool")
            .expect("false bool theorem source proof should check with dependencies")
            .prop(),
        &false_is_bool_prop,
    );
    assert_eq!(
        checked_theorem("is_bool_elim")
            .expect("is-bool eliminator theorem source proof should check with dependencies")
            .prop(),
        &is_bool_elim_prop,
    );
    assert_eq!(
        checked_theorem("bool_distinct")
            .expect("bool distinct theorem source proof should check with dependencies")
            .prop(),
        &bool_distinct_prop,
    );
    assert_eq!(
        checked_theorem("not_congr")
            .expect("not congruence theorem source proof should check with dependencies")
            .prop(),
        &not_congr_prop,
    );
    assert_eq!(
        checked_theorem("and_congr_left")
            .expect("and left congruence theorem source proof should check with dependencies")
            .prop(),
        &and_congr_left_prop,
    );
    assert_eq!(
        checked_theorem("and_congr_right")
            .expect("and right congruence theorem source proof should check with dependencies")
            .prop(),
        &and_congr_right_prop,
    );
    assert_eq!(
        checked_theorem("and_congr")
            .expect("and congruence theorem source proof should check with dependencies")
            .prop(),
        &and_congr_prop,
    );
    assert_eq!(
        checked_theorem("or_congr_left")
            .expect("or left congruence theorem source proof should check with dependencies")
            .prop(),
        &or_congr_left_prop,
    );
    assert_eq!(
        checked_theorem("or_congr_right")
            .expect("or right congruence theorem source proof should check with dependencies")
            .prop(),
        &or_congr_right_prop,
    );
    assert_eq!(
        checked_theorem("or_congr")
            .expect("or congruence theorem source proof should check with dependencies")
            .prop(),
        &or_congr_prop,
    );
    assert_eq!(
        checked_theorem("not_true_elim")
            .expect("not true eliminator theorem source proof should check with dependencies")
            .prop(),
        &not_true_elim_prop,
    );
    assert_eq!(
        checked_theorem("not_false_elim")
            .expect("not false eliminator theorem source proof should check with dependencies")
            .prop(),
        &not_false_elim_prop,
    );
    assert_eq!(
        checked_theorem("if_computes_to_bool")
            .expect("if bool result theorem source proof should check with dependencies")
            .prop(),
        &if_computes_to_bool_prop,
    );
    assert_eq!(
        checked_theorem("if_same")
            .expect("if same theorem source proof should check with dependencies")
            .prop(),
        &if_same_prop,
    );
    assert_eq!(
        checked_theorem("if_not")
            .expect("if not theorem source proof should check with dependencies")
            .prop(),
        &if_not_prop,
    );
    assert_eq!(
        checked_theorem("if_congr_condition")
            .expect("if condition congruence theorem source proof should check with dependencies")
            .prop(),
        &if_congr_condition_prop,
    );
    assert_eq!(
        checked_theorem("if_congr_then")
            .expect("if then-branch congruence theorem source proof should check with dependencies")
            .prop(),
        &if_congr_then_prop,
    );
    assert_eq!(
        checked_theorem("if_congr_else")
            .expect("if else-branch congruence theorem source proof should check with dependencies")
            .prop(),
        &if_congr_else_prop,
    );
    assert_eq!(
        checked_theorem("and_true_intro")
            .expect("and true introduction theorem source proof should check with dependencies")
            .prop(),
        &and_true_intro_prop,
    );
    assert_eq!(
        checked_theorem("and_true_elim_left")
            .expect("and true left eliminator theorem source proof should check with dependencies")
            .prop(),
        &and_true_elim_left_prop,
    );
    assert_eq!(
        checked_theorem("and_true_elim_right")
            .expect("and true right eliminator theorem source proof should check with dependencies")
            .prop(),
        &and_true_elim_right_prop,
    );
    assert_eq!(
        checked_theorem("and_false_cases")
            .expect("and false cases theorem source proof should check with dependencies")
            .prop(),
        &and_false_cases_prop,
    );
    assert_eq!(
        checked_theorem("or_false_intro")
            .expect("or false introduction theorem source proof should check with dependencies")
            .prop(),
        &or_false_intro_prop,
    );
    assert_eq!(
        checked_theorem("or_false_elim_left")
            .expect("or false left eliminator theorem source proof should check with dependencies")
            .prop(),
        &or_false_elim_left_prop,
    );
    assert_eq!(
        checked_theorem("or_false_elim_right")
            .expect("or false right eliminator theorem source proof should check with dependencies")
            .prop(),
        &or_false_elim_right_prop,
    );
    assert_eq!(
        checked_theorem("or_true_cases")
            .expect("or true cases theorem source proof should check with dependencies")
            .prop(),
        &or_true_cases_prop,
    );
    assert_eq!(
        checked_theorem("and_prop_to_bool")
            .expect("and prop-to-bool theorem source proof should check with dependencies")
            .prop(),
        &and_prop_to_bool_prop,
    );
    assert_eq!(
        checked_theorem("and_bool_to_prop")
            .expect("and bool-to-prop theorem source proof should check with dependencies")
            .prop(),
        &and_bool_to_prop_prop,
    );
    assert_eq!(
        checked_theorem("or_prop_to_bool_left")
            .expect("or left prop-to-bool theorem source proof should check with dependencies")
            .prop(),
        &or_prop_to_bool_left_prop,
    );
    assert_eq!(
        checked_theorem("or_prop_to_bool_right")
            .expect("or right prop-to-bool theorem source proof should check with dependencies")
            .prop(),
        &or_prop_to_bool_right_prop,
    );
    assert_eq!(
        checked_theorem("or_bool_to_prop")
            .expect("or bool-to-prop theorem source proof should check with dependencies")
            .prop(),
        &or_bool_to_prop_prop,
    );
    assert_eq!(
        checked_theorem("not_bool_to_absurd")
            .expect("not bool-to-absurd theorem source proof should check with dependencies")
            .prop(),
        &not_bool_to_absurd_prop,
    );
    assert_eq!(
        checked_theorem("not_absurd_to_bool_false")
            .expect("not absurd-to-bool-false theorem source proof should check with dependencies")
            .prop(),
        &not_absurd_to_bool_false_prop,
    );
    assert_eq!(
        checked_theorem("and_absorb_or")
            .expect("and absorption theorem source proof should check with dependencies")
            .prop(),
        &and_absorb_or_prop,
    );
    assert_eq!(
        checked_theorem("or_absorb_and")
            .expect("or absorption theorem source proof should check with dependencies")
            .prop(),
        &or_absorb_and_prop,
    );
    assert_eq!(
        checked_theorem("and_distrib_or_left")
            .expect("left and-over-or distributivity theorem source proof should check with dependencies")
            .prop(),
        &and_distrib_or_left_prop,
    );
    assert_eq!(
        checked_theorem("and_distrib_or_right")
            .expect("right and-over-or distributivity theorem source proof should check with dependencies")
            .prop(),
        &and_distrib_or_right_prop,
    );
    assert_eq!(
        checked_theorem("or_distrib_and_left")
            .expect("left or-over-and distributivity theorem source proof should check with dependencies")
            .prop(),
        &or_distrib_and_left_prop,
    );
    assert_eq!(
        checked_theorem("or_distrib_and_right")
            .expect("right or-over-and distributivity theorem source proof should check with dependencies")
            .prop(),
        &or_distrib_and_right_prop,
    );
    assert_eq!(
        checked_theorem("not_and")
            .expect("not-and De Morgan theorem source proof should check with dependencies")
            .prop(),
        &not_and_prop,
    );
    assert_eq!(
        checked_theorem("not_or")
            .expect("not-or De Morgan theorem source proof should check with dependencies")
            .prop(),
        &not_or_prop,
    );
    assert_eq!(
        checked_theorem("none_is_none")
            .expect("none is none theorem source proof should check with dependencies")
            .prop(),
        &none_is_none_prop,
    );
    assert_eq!(
        checked_theorem("some_is_none")
            .expect("some is none theorem source proof should check with dependencies")
            .prop(),
        &some_is_none_prop,
    );
    assert_eq!(
        checked_theorem("none_is_some")
            .expect("none is some theorem source proof should check with dependencies")
            .prop(),
        &none_is_some_prop,
    );
    assert_eq!(
        checked_theorem("some_is_some")
            .expect("some is some theorem source proof should check with dependencies")
            .prop(),
        &some_is_some_prop,
    );
    assert_eq!(
        checked_theorem("some_congr")
            .expect("some congr theorem source proof should check with dependencies")
            .prop(),
        &some_congr_prop,
    );
    assert_eq!(
        checked_theorem("some_injective")
            .expect("some injective theorem source proof should check with dependencies")
            .prop(),
        &some_injective_prop,
    );
    assert_eq!(
        checked_theorem("option_map_none")
            .expect("option map none theorem source proof should check with dependencies")
            .prop(),
        &option_map_none_prop,
    );
    assert_eq!(
        checked_theorem("option_map_some")
            .expect("option map some theorem source proof should check with dependencies")
            .prop(),
        &option_map_some_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_none")
            .expect("option bind none theorem source proof should check with dependencies")
            .prop(),
        &option_bind_none_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_some")
            .expect("option bind some theorem source proof should check with dependencies")
            .prop(),
        &option_bind_some_prop,
    );
    assert_eq!(
        checked_theorem("unwrap_or_none")
            .expect("unwrap or none theorem source proof should check with dependencies")
            .prop(),
        &unwrap_or_none_prop,
    );
    assert_eq!(
        checked_theorem("unwrap_or_some")
            .expect("unwrap or some theorem source proof should check with dependencies")
            .prop(),
        &unwrap_or_some_prop,
    );
    assert_eq!(
        checked_theorem("option_filter_none")
            .expect("option filter none theorem source proof should check with dependencies")
            .prop(),
        &option_filter_none_prop,
    );
    assert_eq!(
        checked_theorem("option_filter_some_true")
            .expect("option filter some true theorem source proof should check with dependencies")
            .prop(),
        &option_filter_some_true_prop,
    );
    assert_eq!(
        checked_theorem("option_filter_some_false")
            .expect("option filter some false theorem source proof should check with dependencies")
            .prop(),
        &option_filter_some_false_prop,
    );
    assert_eq!(
        checked_theorem("option_map_computes_to_option")
            .expect("option map result-shape theorem source proof should check with dependencies")
            .prop(),
        &option_map_computes_to_option_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_computes_to_option")
            .expect("option bind result-shape theorem source proof should check with dependencies")
            .prop(),
        &option_bind_computes_to_option_prop,
    );
    assert_eq!(
        checked_theorem("unwrap_or_computes_to_value")
            .expect("unwrap or result theorem source proof should check with dependencies")
            .prop(),
        &unwrap_or_computes_to_value_prop,
    );
    assert_eq!(
        checked_theorem("option_filter_computes_to_option")
            .expect(
                "option filter result-shape theorem source proof should check with dependencies"
            )
            .prop(),
        &option_filter_computes_to_option_prop,
    );
    assert_eq!(
        checked_theorem("option_map_identity")
            .expect("option map identity theorem source proof should check with dependencies")
            .prop(),
        &option_map_identity_prop,
    );
    assert_eq!(
        checked_theorem("option_map_compose")
            .expect("option map composition theorem source proof should check with dependencies")
            .prop(),
        &option_map_compose_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_left_identity")
            .expect("option bind left identity theorem source proof should check with dependencies")
            .prop(),
        &option_bind_left_identity_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_right_identity")
            .expect(
                "option bind right identity theorem source proof should check with dependencies"
            )
            .prop(),
        &option_bind_right_identity_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_assoc")
            .expect("option bind associativity theorem source proof should check with dependencies")
            .prop(),
        &option_bind_assoc_prop,
    );
    assert_eq!(
        checked_theorem("option_map_congr_function")
            .expect(
                "option map function congruence theorem source proof should check with dependencies"
            )
            .prop(),
        &option_map_congr_function_prop,
    );
    assert_eq!(
        checked_theorem("option_map_congr_option")
            .expect(
                "option map option congruence theorem source proof should check with dependencies"
            )
            .prop(),
        &option_map_congr_option_prop,
    );
    assert_eq!(
        checked_theorem("option_map_congr_option_computation")
            .expect(
                "option map option computation congruence theorem source proof should check with dependencies"
            )
            .prop(),
        &option_map_congr_option_computation_prop,
    );
    assert_eq!(
        checked_theorem("option_map_congr")
            .expect("option map congruence theorem source proof should check with dependencies")
            .prop(),
        &option_map_congr_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_congr_function")
            .expect(
                "option bind function congruence theorem source proof should check with dependencies"
            )
            .prop(),
        &option_bind_congr_function_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_congr_option")
            .expect(
                "option bind option congruence theorem source proof should check with dependencies"
            )
            .prop(),
        &option_bind_congr_option_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_congr_option_computation")
            .expect(
                "option bind option computation congruence theorem source proof should check with dependencies"
            )
            .prop(),
        &option_bind_congr_option_computation_prop,
    );
    assert_eq!(
        checked_theorem("unwrap_or_congr_default")
            .expect(
                "unwrap-or default congruence theorem source proof should check with dependencies"
            )
            .prop(),
        &unwrap_or_congr_default_prop,
    );
    assert_eq!(
        checked_theorem("unwrap_or_congr_option")
            .expect(
                "unwrap-or option congruence theorem source proof should check with dependencies"
            )
            .prop(),
        &unwrap_or_congr_option_prop,
    );
    assert_eq!(
        checked_theorem("pair_first")
            .expect("pair first theorem source proof should check with dependencies")
            .prop(),
        &pair_first_prop,
    );
    assert_eq!(
        checked_theorem("pair_tail")
            .expect("pair tail theorem source proof should check with dependencies")
            .prop(),
        &pair_tail_prop,
    );
    assert_eq!(
        checked_theorem("pair_second")
            .expect("pair second theorem source proof should check with dependencies")
            .prop(),
        &pair_second_prop,
    );
    assert_eq!(
        checked_theorem("pair_computes_to_list")
            .expect("pair computes-to-list theorem source proof should check with dependencies")
            .prop(),
        &pair_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("pair_computes_to_value")
            .expect("pair computes-to-value theorem source proof should check with dependencies")
            .prop(),
        &pair_computes_to_value_prop,
    );
    assert_eq!(
        checked_theorem("pair_eta")
            .expect("pair eta theorem source proof should check with dependencies")
            .prop(),
        &pair_eta_prop,
    );
    assert_eq!(
        checked_theorem("pair_congr")
            .expect("pair congr theorem source proof should check with dependencies")
            .prop(),
        &pair_congr_prop,
    );
    assert_eq!(
        checked_theorem("pair_first_from_computation")
            .expect("pair first projection theorem source proof should check with dependencies")
            .prop(),
        &pair_first_from_computation_prop,
    );
    assert_eq!(
        checked_theorem("pair_second_from_computation")
            .expect("pair second projection theorem source proof should check with dependencies")
            .prop(),
        &pair_second_from_computation_prop,
    );
    assert_eq!(
        checked_theorem("pair_injective_first")
            .expect("pair first injectivity theorem source proof should check with dependencies")
            .prop(),
        &pair_injective_first_prop,
    );
    assert_eq!(
        checked_theorem("pair_injective_second")
            .expect("pair second injectivity theorem source proof should check with dependencies")
            .prop(),
        &pair_injective_second_prop,
    );
    assert_eq!(
        checked_theorem("pair_injective")
            .expect("pair injectivity theorem source proof should check with dependencies")
            .prop(),
        &pair_injective_prop,
    );
    assert_eq!(
        checked_theorem("list_pair_first_from_computation")
            .expect("list-pair first theorem source proof should check with dependencies")
            .prop(),
        &list_pair_first_from_computation_prop,
    );
    assert_eq!(
        checked_theorem("list_pair_second_from_computation")
            .expect("list-pair second theorem source proof should check with dependencies")
            .prop(),
        &list_pair_second_from_computation_prop,
    );
    assert_eq!(
        checked_theorem("map_nil")
            .expect("map nil theorem source proof should check with dependencies")
            .prop(),
        &map_nil_prop,
    );
    assert_eq!(
        checked_theorem("map_cons")
            .expect("map cons theorem source proof should check with dependencies")
            .prop(),
        &map_cons_prop,
    );
    assert_eq!(
        checked_theorem("map_computes_to_list")
            .expect("map computes theorem source proof should check with dependencies")
            .prop(),
        &map_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("map_replicate")
            .expect("map replicate theorem source proof should check with dependencies")
            .prop(),
        &map_replicate_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_nil")
            .expect("concat-map nil theorem source proof should check with dependencies")
            .prop(),
        &concat_map_nil_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_cons")
            .expect("concat-map cons theorem source proof should check with dependencies")
            .prop(),
        &concat_map_cons_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_computes_to_list")
            .expect("concat-map computes theorem source proof should check with dependencies")
            .prop(),
        &concat_map_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_nil")
            .expect("fold-right nil theorem source proof should check with dependencies")
            .prop(),
        &fold_right_nil_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_cons")
            .expect("fold-right cons theorem source proof should check with dependencies")
            .prop(),
        &fold_right_cons_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_computes_to_value")
            .expect("fold-right computes theorem source proof should check with dependencies")
            .prop(),
        &fold_right_computes_to_value_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_congr")
            .expect("fold-right congruence theorem source proof should check with dependencies")
            .prop(),
        &fold_right_congr_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_nil")
            .expect("fold-left nil theorem source proof should check with dependencies")
            .prop(),
        &fold_left_nil_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_cons")
            .expect("fold-left cons theorem source proof should check with dependencies")
            .prop(),
        &fold_left_cons_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_computes_to_value")
            .expect("fold-left computes theorem source proof should check with dependencies")
            .prop(),
        &fold_left_computes_to_value_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_congr")
            .expect("fold-left congruence theorem source proof should check with dependencies")
            .prop(),
        &fold_left_congr_prop,
    );
    assert_eq!(
        checked_theorem("zip_left_nil")
            .expect("zip left nil theorem source proof should check with dependencies")
            .prop(),
        &zip_left_nil_prop,
    );
    assert_eq!(
        checked_theorem("zip_right_nil")
            .expect("zip right nil theorem source proof should check with dependencies")
            .prop(),
        &zip_right_nil_prop,
    );
    assert_eq!(
        checked_theorem("zip_cons")
            .expect("zip cons theorem source proof should check with dependencies")
            .prop(),
        &zip_cons_prop,
    );
    assert_eq!(
        checked_theorem("zip_computes_to_list")
            .expect("zip computes theorem source proof should check with dependencies")
            .prop(),
        &zip_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("zip_pair_shape")
            .expect("zip pair-shape theorem source proof should check with dependencies")
            .prop(),
        &zip_pair_shape_prop,
    );
    assert_eq!(
        checked_theorem("unzip_nil")
            .expect("unzip nil theorem source proof should check with dependencies")
            .prop(),
        &unzip_nil_prop,
    );
    assert_eq!(
        checked_theorem("unzip_cons")
            .expect("unzip cons theorem source proof should check with dependencies")
            .prop(),
        &unzip_cons_prop,
    );
    assert_eq!(
        checked_theorem("unzip_pair_shape")
            .expect("unzip pair-shape theorem source proof should check with dependencies")
            .prop(),
        &unzip_pair_shape_prop,
    );
    assert_eq!(
        checked_theorem("zip_unzip")
            .expect("zip unzip theorem source proof should check with dependencies")
            .prop(),
        &zip_unzip_prop,
    );
    assert_eq!(
        checked_theorem("unzip_zip")
            .expect("unzip zip theorem source proof should check with dependencies")
            .prop(),
        &unzip_zip_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_as_map_zip")
            .expect("zip with as map zip theorem source proof should check with dependencies")
            .prop(),
        &zip_with_as_map_zip_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_left_nil")
            .expect("zip-with left nil theorem source proof should check with dependencies")
            .prop(),
        &zip_with_left_nil_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_right_nil")
            .expect("zip-with right nil theorem source proof should check with dependencies")
            .prop(),
        &zip_with_right_nil_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_cons")
            .expect("zip-with cons theorem source proof should check with dependencies")
            .prop(),
        &zip_with_cons_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_computes_to_list")
            .expect("zip-with computes theorem source proof should check with dependencies")
            .prop(),
        &zip_with_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("filter_nil")
            .expect("filter nil theorem source proof should check with dependencies")
            .prop(),
        &filter_nil_prop,
    );
    assert_eq!(
        checked_theorem("filter_cons_true")
            .expect("filter true cons theorem source proof should check with dependencies")
            .prop(),
        &filter_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("filter_cons_false")
            .expect("filter false cons theorem source proof should check with dependencies")
            .prop(),
        &filter_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("filter_computes_to_list")
            .expect("filter computes theorem source proof should check with dependencies")
            .prop(),
        &filter_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("filter_congr")
            .expect("filter congruence theorem source proof should check with dependencies")
            .prop(),
        &filter_congr_prop,
    );
    assert_eq!(
        checked_theorem("reject_nil")
            .expect("reject nil theorem source proof should check with dependencies")
            .prop(),
        &reject_nil_prop,
    );
    assert_eq!(
        checked_theorem("reject_cons_true")
            .expect("reject true cons theorem source proof should check with dependencies")
            .prop(),
        &reject_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("reject_cons_false")
            .expect("reject false cons theorem source proof should check with dependencies")
            .prop(),
        &reject_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("reject_computes_to_list")
            .expect("reject computes theorem source proof should check with dependencies")
            .prop(),
        &reject_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("filter_append")
            .expect("filter append theorem source proof should check with dependencies")
            .prop(),
        &filter_append_prop,
    );
    assert_eq!(
        checked_theorem("reject_append")
            .expect("reject append theorem source proof should check with dependencies")
            .prop(),
        &reject_append_prop,
    );
    assert_eq!(
        checked_theorem("filter_idempotent")
            .expect("filter idempotence theorem source proof should check with dependencies")
            .prop(),
        &filter_idempotent_prop,
    );
    assert_eq!(
        checked_theorem("reject_idempotent")
            .expect("reject idempotence theorem source proof should check with dependencies")
            .prop(),
        &reject_idempotent_prop,
    );
    assert_eq!(
        checked_theorem("partition_nil")
            .expect("partition nil theorem source proof should check with dependencies")
            .prop(),
        &partition_nil_prop,
    );
    assert_eq!(
        checked_theorem("partition_cons_true")
            .expect("partition true cons theorem source proof should check with dependencies")
            .prop(),
        &partition_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("partition_cons_false")
            .expect("partition false cons theorem source proof should check with dependencies")
            .prop(),
        &partition_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("partition_computes_to_pair")
            .expect("partition pair result theorem source proof should check with dependencies")
            .prop(),
        &partition_computes_to_pair_prop,
    );
    assert_eq!(
        checked_theorem("partition_first_filter")
            .expect(
                "partition first projection theorem source proof should check with dependencies"
            )
            .prop(),
        &partition_first_filter_prop,
    );
    assert_eq!(
        checked_theorem("partition_second_filter_false")
            .expect(
                "partition second projection theorem source proof should check with dependencies"
            )
            .prop(),
        &partition_second_filter_false_prop,
    );
    assert_eq!(
        checked_theorem("partition_second_reject")
            .expect("partition second reject theorem source proof should check with dependencies")
            .prop(),
        &partition_second_reject_prop,
    );
    assert_eq!(
        checked_theorem("any_nil")
            .expect("any nil theorem source proof should check with dependencies")
            .prop(),
        &any_nil_prop,
    );
    assert_eq!(
        checked_theorem("any_cons_true")
            .expect("any true cons theorem source proof should check with dependencies")
            .prop(),
        &any_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("any_cons_false")
            .expect("any false cons theorem source proof should check with dependencies")
            .prop(),
        &any_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("any_computes_to_bool")
            .expect("any computes theorem source proof should check with dependencies")
            .prop(),
        &any_computes_to_bool_prop,
    );
    assert_eq!(
        checked_theorem("any_append")
            .expect("any append theorem source proof should check with dependencies")
            .prop(),
        &any_append_prop,
    );
    assert_eq!(
        checked_theorem("all_true_implies_not_any_false")
            .expect("all true any-not theorem source proof should check with dependencies")
            .prop(),
        &all_true_implies_not_any_false_prop,
    );
    assert_eq!(
        checked_theorem("any_true_implies_not_all_false")
            .expect("any true all-not theorem source proof should check with dependencies")
            .prop(),
        &any_true_implies_not_all_false_prop,
    );
    assert_eq!(
        checked_theorem("find_nil")
            .expect("find nil theorem source proof should check with dependencies")
            .prop(),
        &find_nil_prop,
    );
    assert_eq!(
        checked_theorem("find_cons_true")
            .expect("find true cons theorem source proof should check with dependencies")
            .prop(),
        &find_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("find_cons_false")
            .expect("find false cons theorem source proof should check with dependencies")
            .prop(),
        &find_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("find_append")
            .expect("find append theorem source proof should check with dependencies")
            .prop(),
        &find_append_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_true_true")
            .expect("value-eq true theorem source proof should check with dependencies")
            .prop(),
        &value_eq_true_true_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_true_false")
            .expect("value-eq false theorem source proof should check with dependencies")
            .prop(),
        &value_eq_true_false_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_nil")
            .expect("value-eq nil theorem source proof should check with dependencies")
            .prop(),
        &value_eq_nil_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_nil_cons")
            .expect("value-eq nil cons theorem source proof should check with dependencies")
            .prop(),
        &value_eq_nil_cons_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_cons_nil")
            .expect("value-eq cons nil theorem source proof should check with dependencies")
            .prop(),
        &value_eq_cons_nil_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_cons")
            .expect("value-eq cons theorem source proof should check with dependencies")
            .prop(),
        &value_eq_cons_prop,
    );
    assert_eq!(
        checked_theorem("value_kind_symbol_implies_is_symbol")
            .expect("symbol classifier bridge theorem source proof should check with dependencies")
            .prop(),
        &value_kind_symbol_implies_is_symbol_prop,
    );
    assert_eq!(
        checked_theorem("value_kind_lambda_implies_is_lambda")
            .expect("lambda classifier bridge theorem source proof should check with dependencies")
            .prop(),
        &value_kind_lambda_implies_is_lambda_prop,
    );
    assert_eq!(
        checked_theorem("is_symbol_true_implies_is_lambda_false")
            .expect("symbol kind theorem source proof should check with dependencies")
            .prop(),
        &is_symbol_true_implies_is_lambda_false_prop,
    );
    assert_eq!(
        checked_theorem("is_symbol_true_implies_is_list_value_false")
            .expect("symbol/list kind theorem source proof should check with dependencies")
            .prop(),
        &is_symbol_true_implies_is_list_value_false_prop,
    );
    assert_eq!(
        checked_theorem("is_lambda_true_implies_is_symbol_false")
            .expect("lambda/symbol kind theorem source proof should check with dependencies")
            .prop(),
        &is_lambda_true_implies_is_symbol_false_prop,
    );
    assert_eq!(
        checked_theorem("is_lambda_true_implies_is_list_value_false")
            .expect("lambda/list kind theorem source proof should check with dependencies")
            .prop(),
        &is_lambda_true_implies_is_list_value_false_prop,
    );
    assert_eq!(
        checked_theorem("is_list_value_true_implies_is_symbol_false")
            .expect("list/symbol kind theorem source proof should check with dependencies")
            .prop(),
        &is_list_value_true_implies_is_symbol_false_prop,
    );
    assert_eq!(
        checked_theorem("is_list_value_true_implies_is_lambda_false")
            .expect("list/lambda kind theorem source proof should check with dependencies")
            .prop(),
        &is_list_value_true_implies_is_lambda_false_prop,
    );
    assert_eq!(
        checked_theorem("value_kind_exactly_one")
            .expect("exactly-one kind theorem source proof should check with dependencies")
            .prop(),
        &value_kind_exactly_one_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_comparable_symbol")
            .expect("symbol comparability theorem source proof should check with dependencies")
            .prop(),
        &value_eq_comparable_symbol_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_comparable_nil")
            .expect("nil comparability theorem source proof should check with dependencies")
            .prop(),
        &value_eq_comparable_nil_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_comparable_cons")
            .expect("cons comparability theorem source proof should check with dependencies")
            .prop(),
        &value_eq_comparable_cons_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_comparable_no_lambdas")
            .expect(
                "comparability lambda guard theorem source proof should check with dependencies"
            )
            .prop(),
        &value_eq_comparable_no_lambdas_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_true_implies_not_lambdas")
            .expect("value-eq lambda guard theorem source proof should check with dependencies")
            .prop(),
        &value_eq_true_implies_not_lambdas_prop,
    );
    assert_eq!(
        checked_theorem("value_non_symbol_non_lambda_non_bv32_is_list")
            .expect("value classification theorem source proof should check with dependencies")
            .prop(),
        &value_non_symbol_non_lambda_non_bv32_is_list_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_left_non_symbol_true_implies_lists")
            .expect("value-eq non-symbol list theorem source proof should check with dependencies")
            .prop(),
        &value_eq_left_non_symbol_true_implies_lists_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_left_symbol_true")
            .expect("value-eq left symbol theorem source proof should check with dependencies")
            .prop(),
        &value_eq_left_symbol_true_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_left_symbol_sound")
            .expect(
                "value-eq left symbol soundness theorem source proof should check with dependencies"
            )
            .prop(),
        &value_eq_left_symbol_sound_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_cons_true_elim")
            .expect("value-eq cons elimination theorem source proof should check with dependencies")
            .prop(),
        &value_eq_cons_true_elim_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_cons_false_cases")
            .expect("value-eq cons false-cases theorem source proof should check with dependencies")
            .prop(),
        &value_eq_cons_false_cases_prop,
    );
    assert_eq!(
        checked_theorem("cons_congr")
            .expect("cons congruence theorem source proof should check with dependencies")
            .prop(),
        &cons_congr_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_sound")
            .expect("value-eq soundness theorem source proof should check with dependencies")
            .prop(),
        &value_eq_sound_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_refl")
            .expect("value-eq reflexivity theorem source proof should check with dependencies")
            .prop(),
        &value_eq_refl_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_true_implies_comparable_left")
            .expect(
                "value-eq left comparability theorem source proof should check with dependencies"
            )
            .prop(),
        &value_eq_true_implies_comparable_left_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_true_implies_comparable_right")
            .expect(
                "value-eq right comparability theorem source proof should check with dependencies"
            )
            .prop(),
        &value_eq_true_implies_comparable_right_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_symm")
            .expect("value-eq symmetry theorem source proof should check with dependencies")
            .prop(),
        &value_eq_symm_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_trans")
            .expect("value-eq transitivity theorem source proof should check with dependencies")
            .prop(),
        &value_eq_trans_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_complete_for_comparable_values")
            .expect("value-eq completeness theorem source proof should check with dependencies")
            .prop(),
        &value_eq_complete_for_comparable_values_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_false_implies_not_equal_for_comparable_values")
            .expect("value-eq disequality theorem source proof should check with dependencies")
            .prop(),
        &value_eq_false_implies_not_equal_for_comparable_values_prop,
    );
    assert_eq!(
        checked_theorem("symbol_not_list")
            .expect("symbol/list disequality theorem source proof should check with dependencies")
            .prop(),
        &symbol_not_list_prop,
    );
    assert_eq!(
        checked_theorem("symbol_not_lambda")
            .expect("symbol/lambda disequality theorem source proof should check with dependencies")
            .prop(),
        &symbol_not_lambda_prop,
    );
    assert_eq!(
        checked_theorem("list_not_lambda")
            .expect("list/lambda disequality theorem source proof should check with dependencies")
            .prop(),
        &list_not_lambda_prop,
    );
    assert_eq!(
        checked_theorem("member_nil")
            .expect("member nil theorem source proof should check with dependencies")
            .prop(),
        &member_nil_prop,
    );
    assert_eq!(
        checked_theorem("member_cons_true")
            .expect("member true cons theorem source proof should check with dependencies")
            .prop(),
        &member_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("member_cons_false")
            .expect("member false cons theorem source proof should check with dependencies")
            .prop(),
        &member_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("member_computes_to_bool")
            .expect("member computes to bool theorem source proof should check with dependencies")
            .prop(),
        &member_computes_to_bool_prop,
    );
    assert_eq!(
        checked_theorem("member_is_bool_for_comparable_value")
            .expect("member comparable bool theorem source proof should check with dependencies")
            .prop(),
        &member_is_bool_for_comparable_value_prop,
    );
    assert_eq!(
        checked_theorem("member_cons_or")
            .expect("member cons or theorem source proof should check with dependencies")
            .prop(),
        &member_cons_or_prop,
    );
    assert_eq!(
        checked_theorem("member_append")
            .expect("member append theorem source proof should check with dependencies")
            .prop(),
        &member_append_prop,
    );
    assert_eq!(
        checked_theorem("elem_index_cons_some_cases")
            .expect(
                "elem-index cons some cases theorem source proof should check with dependencies"
            )
            .prop(),
        &elem_index_cons_some_cases_prop,
    );
    assert_eq!(
        checked_theorem("elem_index_append_left")
            .expect("elem-index append left theorem source proof should check with dependencies")
            .prop(),
        &elem_index_append_left_prop,
    );
    assert_eq!(
        checked_theorem("elem_index_cons_none_parts")
            .expect(
                "elem-index cons none parts theorem source proof should check with dependencies"
            )
            .prop(),
        &elem_index_cons_none_parts_prop,
    );
    assert_eq!(
        checked_theorem("elem_index_append_right")
            .expect("elem-index append right theorem source proof should check with dependencies")
            .prop(),
        &elem_index_append_right_prop,
    );
    assert_eq!(
        checked_theorem("all_nil")
            .expect("all nil theorem source proof should check with dependencies")
            .prop(),
        &all_nil_prop,
    );
    assert_eq!(
        checked_theorem("all_cons_true")
            .expect("all true cons theorem source proof should check with dependencies")
            .prop(),
        &all_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("all_cons_false")
            .expect("all false cons theorem source proof should check with dependencies")
            .prop(),
        &all_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("all_computes_to_bool")
            .expect("all computes theorem source proof should check with dependencies")
            .prop(),
        &all_computes_to_bool_prop,
    );
    assert_eq!(
        checked_theorem("all_cons_true_parts")
            .expect("all true cons parts theorem source proof should check with dependencies")
            .prop(),
        &all_cons_true_parts_prop,
    );
    assert_eq!(
        checked_theorem("all_append")
            .expect("all append theorem source proof should check with dependencies")
            .prop(),
        &all_append_prop,
    );
    assert_eq!(
        checked_theorem("map_identity")
            .expect("map identity theorem source proof should check with dependencies")
            .prop(),
        &map_identity_prop,
    );
    assert_eq!(
        checked_theorem("map_compose")
            .expect("map compose theorem source proof should check with dependencies")
            .prop(),
        &map_compose_prop,
    );
    assert_eq!(
        checked_theorem("map_congr")
            .expect("map congruence theorem source proof should check with dependencies")
            .prop(),
        &map_congr_prop,
    );
    assert_eq!(
        checked_theorem("map_append")
            .expect("map append theorem source proof should check with dependencies")
            .prop(),
        &map_append_prop,
    );
    assert_eq!(
        checked_theorem("map_snoc")
            .expect("map snoc theorem source proof should check with dependencies")
            .prop(),
        &map_snoc_prop,
    );
    assert_eq!(
        checked_theorem("map_take")
            .expect("map take theorem source proof should check with dependencies")
            .prop(),
        &map_take_prop,
    );
    assert_eq!(
        checked_theorem("map_drop")
            .expect("map drop theorem source proof should check with dependencies")
            .prop(),
        &map_drop_prop,
    );
    assert_eq!(
        checked_theorem("option_map_nth")
            .expect("option-map nth theorem source proof should check with dependencies")
            .prop(),
        &option_map_nth_prop,
    );
    assert_eq!(
        checked_theorem("option_map_find")
            .expect("option-map find theorem source proof should check with dependencies")
            .prop(),
        &option_map_find_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_find_none")
            .expect("option-bind find none theorem source proof should check with dependencies")
            .prop(),
        &option_bind_find_none_prop,
    );
    assert_eq!(
        checked_theorem("option_bind_find_some")
            .expect("option-bind find some theorem source proof should check with dependencies")
            .prop(),
        &option_bind_find_some_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_singleton")
            .expect("concat-map singleton theorem source proof should check with dependencies")
            .prop(),
        &concat_map_singleton_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_append")
            .expect("concat-map append theorem source proof should check with dependencies")
            .prop(),
        &concat_map_append_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_as_concat_map")
            .expect("concat-map-as-concat-map theorem source proof should check with dependencies")
            .prop(),
        &concat_map_as_concat_map_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_cons_nil")
            .expect("fold-right cons theorem source proof should check with dependencies")
            .prop(),
        &fold_right_cons_nil_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_append")
            .expect("fold-right append theorem source proof should check with dependencies")
            .prop(),
        &fold_right_append_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_append")
            .expect("fold-left append theorem source proof should check with dependencies")
            .prop(),
        &fold_left_append_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_map")
            .expect("fold-right map theorem source proof should check with dependencies")
            .prop(),
        &fold_right_map_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_map")
            .expect("fold-left map theorem source proof should check with dependencies")
            .prop(),
        &fold_left_map_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_reverse_acc")
            .expect(
                "fold-left reverse accumulator theorem source proof should check with dependencies"
            )
            .prop(),
        &fold_left_reverse_acc_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_reverse")
            .expect("fold-left reverse theorem source proof should check with dependencies")
            .prop(),
        &fold_left_reverse_prop,
    );
    assert_eq!(
        checked_theorem("append_take_drop")
            .expect("append take/drop theorem source proof should check with dependencies")
            .prop(),
        &append_take_drop_prop,
    );
}

#[test]
fn prelude_theory_instantiates_named_reverse_theorem() {
    let theory = theory();
    let reverse = theory
        .known(theorem("reverse_computes_to_list"))
        .expect("reverse theorem should be defined");
    let with_predicate = theory
        .forall_elim(&reverse, list_tests::nil())
        .expect("known theorem should instantiate in its theory");
    let nil_is_list = Theorem::from_proof(
        Proof::Primitive(is_list(list_tests::nil())),
        is_list(list_tests::nil()),
    )
    .expect("nil should prove is-list as a primitive proposition");
    let instantiated = theory
        .implies_elim(&with_predicate, &nil_is_list)
        .expect("reverse theorem premise should discharge for nil");

    assert_eq!(
        instantiated.prop(),
        &computes_to_list(
            list_tests::reverse_computes_to_list_source_result_symbol(),
            list_tests::reverse_call(list_tests::nil()),
        )
    );
}
