# Prelude First Layer Roadmap

This document describes the intended theorem coverage for the first layer of
the standard prelude: the ordinary programming and proof substrate before a
gradual typing layer is built on top.

The scope for this pass is:

- natural numbers
- lists
- boolean logic
- options
- equality
- pairs

Association lists, environments, records, and typing-specific structures are
intentionally out of scope for now.

This is a coverage roadmap, not a completion ledger. Before implementing a
theorem listed here, check the source first and either reuse the existing
theorem or adjust the roadmap if the theorem is already covered under a better
name.

## General Conventions

Every prelude function should have the basic operational facts that make it
usable in later proofs:

- unfold theorems for each constructor-shaped input
- result-shape theorems, such as computing to a list, bool, option, pair, or
  nat value
- congruence theorems when arguments compute to equal values
- interaction theorems with the core functions in its domain
- simp-oriented theorems whose right side is the canonical form

Computational booleans are currently ordinary strict computations. Keep that
limitation visible in theorem statements by requiring explicit `is-bool`
premises where an argument must already compute to `:true` or `:false`.

## Boolean Logic

Basic boolean values:

- `true_is_bool`
- `false_is_bool`
- `is_bool_elim`: from `is-bool b`, split into `b = :true` or `b = :false`
- `bool_distinct`: `:true = :false` implies `absurd`

`not`:

- `not_true`
- `not_false`
- `not_computes_to_bool`
- `not_not`
- `not_true_elim`: if `(not b)` computes to `:true`, then `b` computes to
  `:false`
- `not_false_elim`: if `(not b)` computes to `:false`, then `b` computes to
  `:true`
- `not_congr`: equal boolean inputs give equal `not` results

`and`:

- `and_true_left`
- `and_false_left`
- `and_true_right`
- `and_false_right`
- `and_computes_to_bool`
- `and_comm`
- `and_assoc`
- `and_idempotent`
- `and_true_intro`: if both inputs compute to `:true`, their `and` computes to
  `:true`
- `and_true_elim_left`
- `and_true_elim_right`
- `and_false_cases`: if `and` computes to `:false`, at least one input computes
  to `:false`
- `and_absorb_or`: `and a (or a b) = a`
- `and_distrib_or_left`
- `and_distrib_or_right`

`or`:

- `or_true_left`
- `or_false_left`
- `or_true_right`
- `or_false_right`
- `or_computes_to_bool`
- `or_comm`
- `or_assoc`
- `or_idempotent`
- `or_true_cases`: if `or` computes to `:true`, at least one input computes to
  `:true`
- `or_false_intro`: if both inputs compute to `:false`, their `or` computes to
  `:false`
- `or_false_elim_left`
- `or_false_elim_right`
- `or_absorb_and`: `or a (and a b) = a`
- `or_distrib_and_left`
- `or_distrib_and_right`

Boolean/propositional bridges:

- `and_prop_to_bool`: from proofs of computational truth of both inputs, prove
  computational truth of `and`
- `and_bool_to_prop`: from computational truth of `and`, recover both truth
  proofs
- `or_prop_to_bool_left`
- `or_prop_to_bool_right`
- `or_bool_to_prop`: from computational truth of `or`, recover a propositional
  disjunction
- `not_bool_to_absurd`: from `b = :true` and `(not b) = :true`, prove `absurd`
- `not_absurd_to_bool_false`: if assuming `b = :true` gives `absurd`, prove
  `b = :false` under an `is-bool b` premise
- De Morgan laws for computational booleans:
  `not (and a b) = or (not a) (not b)` and
  `not (or a b) = and (not a) (not b)`

`if`:

- `if_true`
- `if_false`
- `if_condition_true`
- `if_condition_false`
- `if_computes_to_bool`: if both branches compute to booleans, the `if`
  computes to a boolean
- `if_same`: `(if condition branch branch) = branch` when the condition is a
  boolean
- `if_not`: `(if (not condition) then else) = (if condition else then)`
- `if_congr_condition`
- `if_congr_then`
- `if_congr_else`
- inversion theorems for true and false results with simple branch shapes

## Options

Core option encoding:

- `none_is_none`
- `some_is_none`
- `none_is_some`
- `some_is_some`
- `some_tag_from_computation`
- `some_value_from_computation`
- `some_none_absurd`
- `none_some_absurd`
- `some_injective`: `some x = some y` implies `x = y`
- `some_congr`: `x = y` implies `some x = some y`
- `option_cases`: every valid option is either `none` or `some value`
- `option_result_shape`: option-producing functions compute to either `none`
  or `some value`

Option helpers to add:

- `option-map`
- `option-bind`
- `unwrap-or`
- `option-filter`

`option-map` theorems:

- `option_map_none`
- `option_map_some`
- `option_map_computes_to_option`
- `option_map_identity`
- `option_map_compose`
- `option_map_congr_function`
- `option_map_congr_option`

`option-bind` theorems:

- `option_bind_none`
- `option_bind_some`
- `option_bind_computes_to_option`
- `option_bind_left_identity`
- `option_bind_right_identity`
- `option_bind_assoc`
- `option_bind_congr_function`
- `option_bind_congr_option`

`unwrap-or` theorems:

- `unwrap_or_none`
- `unwrap_or_some`
- `unwrap_or_computes_to_value`
- `unwrap_or_congr_default`
- `unwrap_or_congr_option`

Relationships with existing option-producing functions:

- `nth_zero_cons_some`
- `nth_out_of_bounds_none`
- `find_some_implies_any_true`
- `find_none_implies_any_false`
- `elem_index_some_implies_member_true`
- `elem_index_none_implies_member_false`
- `option_map_find`
- `option_map_nth`
- `option_bind_find`

## Pairs

Pair encoding:

- `pair first second = (cons first (cons second nil))`
- `first pair = head pair`
- `second pair = head (tail pair)`
- `is-pair` if we decide a computational predicate is useful

Pair theorems:

- `pair_first`
- `pair_second`
- `pair_eta`: a pair is equal to the pair of its projections
- `pair_congr`
- `pair_injective_first`
- `pair_injective_second`
- `pair_injective`: equality of pairs gives equality of both components
- `pair_computes_to_list`
- `pair_computes_to_value`
- `is_pair_pair`
- `is_pair_nil_false`
- `is_pair_singleton_false`
- `is_pair_cons_cons_nil_true`
- `is_pair_cons_cons_cons_false`

Relationships with existing pair-shaped APIs:

- `split_at_pair_eta`
- `split_at_first_take`
- `split_at_second_drop`
- `partition_first_filter`
- `partition_second_reject`
- `zip_pair_shape`
- `unzip_pair_shape`

## Lists

Constructor and destructor basics:

- `nil_is_list`
- `cons_is_list`
- `cons_head`
- `cons_tail`
- `nil_not_cons`
- `cons_not_nil`
- `cons_injective_head`
- `cons_injective_tail`
- `cons_injective`
- `list_eta`: a nonempty list is `cons (head list) (tail list)`

Append and reverse:

- `append_nil_returns_right`
- `append_right_nil`
- `append_cons`
- `append_assoc`
- `append_computes_to_list`
- `append_congr_left`
- `append_congr_right`
- `reverse_nil`
- `reverse_singleton`
- `reverse_cons`
- `reverse_append`
- `reverse_double`
- `reverse_computes_to_list`
- `reverse_acc_append`
- `reverse_acc_reverse`

Length:

- `length_nil`
- `length_cons`
- `length_singleton`
- `length_append`
- `length_reverse`
- `length_map`
- `length_filter_le`
- `length_take`
- `length_drop`
- `length_take_add_length_drop`
- `length_replicate`
- `length_zip_min`
- `length_concat`

Map and concat-map:

- `map_nil`
- `map_cons`
- `map_computes_to_list`
- `map_identity`
- `map_compose`
- `map_append`
- `map_reverse`
- `map_take`
- `map_drop`
- `concat_map_nil`
- `concat_map_cons`
- `concat_map_computes_to_list`
- `concat_map_singleton`
- `concat_map_append`
- `concat_map_as_concat_map`

Folds:

- `fold_right_nil`
- `fold_right_cons`
- `fold_right_computes_to_value`
- `fold_left_nil`
- `fold_left_cons`
- `fold_left_computes_to_value`
- `fold_right_cons_nil`
- `fold_left_reverse_acc`
- `fold_left_reverse`
- `fold_right_append`
- `fold_left_append`
- `fold_right_map`
- `fold_left_map`

Filter, reject, partition:

- `filter_nil`
- `filter_cons_true`
- `filter_cons_false`
- `filter_computes_to_list`
- `reject_nil`
- `reject_cons_true`
- `reject_cons_false`
- `reject_computes_to_list`
- `partition_second_filter_false`
- `partition_append_filter_reject`
- `partition_all_true`
- `partition_all_false`
- `partition_first_filter`
- `partition_second_reject`
- `filter_append`
- `reject_append`
- `filter_idempotent`
- `reject_idempotent`

Any, all, find:

- `any_nil`
- `any_cons_true`
- `any_cons_false`
- `any_cons_or`
- `any_computes_to_bool`
- `all_nil`
- `all_cons_true`
- `all_cons_false`
- `all_cons_and`
- `all_computes_to_bool`
- `find_nil`
- `find_cons_true`
- `find_cons_false`
- `find_cons_branch`
- `find_computes_to_option`
- `any_false_implies_find_none`
- `any_true_implies_find_some`
- `find_none_implies_any_false`
- `find_some_implies_any_true`
- `all_true_implies_not_any_false`
- `any_true_implies_not_all_false`
- `any_append`
- `all_append`
- `find_append`

Membership and indexing:

- `member_nil`
- `member_cons_true`
- `member_cons_false`
- `member_computes_to_bool`
- `elem_index_nil`
- `elem_index_cons_true`
- `elem_index_cons_false_none`
- `elem_index_cons_false_some`
- `elem_index_computes_to_option`
- `member_false_implies_elem_index_none`
- `member_true_implies_elem_index_some`
- `elem_index_none_implies_member_false`
- `elem_index_some_implies_member_true`
- `nth_zero_nil`
- `nth_zero_cons`
- `nth_cons_nil`
- `nth_cons_cons`
- `nth_computes_to_option`
- `nth_after_split_at`
- `nth_zero_after_drop`
- `member_append`
- `elem_index_append_left`
- `elem_index_append_right`

Take, drop, split-at:

- `take_zero`
- `take_nil`
- `take_cons`
- `take_computes_to_list`
- `drop_zero`
- `drop_nil`
- `drop_cons`
- `drop_computes_to_list`
- `append_take_drop`
- `take_length`
- `drop_length`
- `take_take`
- `drop_drop`
- `take_drop_commute`
- `split_at_computes_to_pair`
- `split_at_first_take`
- `split_at_second_drop`
- `split_at_append`
- `split_at_pair_eta`

Replication, zipping, and sequence helpers:

- `replicate_zero`
- `replicate_cons`
- `replicate_computes_to_list`
- `length_replicate`
- `map_replicate`
- `take_replicate`
- `drop_replicate`
- `zip_left_nil`
- `zip_right_nil`
- `zip_cons`
- `zip_computes_to_list`
- `unzip_nil`
- `unzip_cons`
- `zip_unzip`
- `unzip_zip`
- `zip_with_left_nil`
- `zip_with_right_nil`
- `zip_with_cons`
- `zip_with_computes_to_list`
- `zip_with_as_map_zip`
- `intersperse_nil`
- `intersperse_singleton`
- `intersperse_cons_cons`
- `intersperse_computes_to_list`
- `intercalate_nil`
- `intercalate_singleton`
- `intercalate_cons_cons`
- `intercalate_computes_to_list`
- `concat_nil`
- `concat_cons`
- `concat_append`
- `concat_computes_to_list`

Small list predicates:

- `last_nil_errors`
- `last_singleton`
- `last_cons`
- `init_nil_errors`
- `init_singleton`
- `init_cons`
- `null_nil`
- `null_cons`
- `is_singleton_nil`
- `is_singleton_singleton`
- `is_singleton_cons`

## Natural Numbers

Representation and constructors:

- `zero_eq_nil`
- `zero_computes_to_list`
- `zero_is_nat_value`
- `succ_zero`
- `succ_computes_to_list`
- `succ_preserves_nat_value`
- `succ_injective`
- `zero_ne_succ`
- `is_nat_value_nil`
- `is_nat_value_cons`
- `is_nat_value_tail`
- `nat_induction` as a source-level theorem if useful

Zero and predecessor:

- `is_zero_zero`
- `is_zero_succ`
- `is_zero_computes_to_bool`
- `pred_zero`
- `pred_succ`
- `pred_computes_to_list`
- `pred_preserves_nat_value`
- `pred_succ_inverse`
- `succ_pred_inverse_for_nonzero`

Addition:

- `add_is_append`
- `add_zero_left`
- `add_zero_right`
- `add_succ_left`
- `add_succ_right`
- `add_computes_to_list`
- `add_preserves_nat_value`
- `add_assoc`
- `add_comm`
- `add_left_cancel`
- `add_right_cancel`
- `add_left_eq_zero`
- `add_right_eq_zero`
- `add_eq_zero_cases`

Subtraction:

- `sub_zero_right`
- `sub_zero_left`
- `sub_succ_succ`
- `sub_self`
- `sub_computes_to_list`
- `sub_preserves_nat_value`
- `add_sub_cancel_right`
- `add_sub_cancel_left`
- `sub_add_cancel`
- `sub_eq_zero_of_le`
- `sub_pos_of_lt`
- `sub_monotone_left`
- `sub_monotone_right`

Multiplication:

- `mul_zero_left`
- `mul_zero_right`
- `mul_one_left`
- `mul_one_right`
- `mul_succ_left`
- `mul_succ_right`
- `mul_computes_to_list`
- `mul_preserves_nat_value`
- `mul_comm`
- `mul_assoc`
- `mul_add_left_distrib`
- `mul_add_right_distrib`
- `mul_left_cancel_positive`
- `mul_right_cancel_positive`
- `mul_eq_zero_cases`

Comparison and order:

- `nat_eq_refl`
- `nat_eq_symm`
- `nat_eq_trans`
- `nat_eq_computes_to_bool`
- `nat_eq_true_implies_equal`
- `nat_eq_false_implies_not_equal`
- `nat_le_refl`
- `nat_le_zero_left`
- `nat_le_zero_right`
- `nat_le_succ_right`
- `nat_le_succ_succ`
- `nat_le_trans`
- `nat_le_antisymm`
- `nat_le_total`
- `nat_le_computes_to_bool`
- `nat_lt_irrefl`
- `nat_lt_succ_self`
- `nat_lt_succ_succ`
- `nat_lt_trans`
- `nat_lt_as_le_and_not_eq`
- `nat_lt_computes_to_bool`
- `nat_lt_implies_le`
- `nat_le_and_ne_implies_lt`
- `nat_le_add_right`
- `nat_le_add_left`
- `nat_lt_add_right`
- `nat_lt_add_left`
- `nat_le_add_cancel_left`
- `nat_le_add_cancel_right`
- `nat_lt_add_cancel_left`
- `nat_lt_add_cancel_right`
- `nat_le_mul_positive_right`
- `nat_le_mul_positive_left`
- `nat_lt_mul_positive_right`
- `nat_lt_mul_positive_left`

Range:

- `range_zero`
- `range_cons`
- `range_succ`
- `range_computes_to_list`
- `length_range`
- `map_succ_range`
- `member_range_iff_lt`

Potential later nat helpers:

- `min`
- `max`
- `min_left`
- `min_right`
- `min_comm`
- `min_assoc`
- `max_left`
- `max_right`
- `max_comm`
- `max_assoc`
- `min_le_left`
- `min_le_right`
- `left_le_max`
- `right_le_max`
- `min_add_distrib`
- `max_add_distrib`

Division and modulo should probably wait until the first-layer arithmetic and
order story feels settled.

## Equality

Kernel equality:

- reflexivity, symmetry, transitivity, and rewrite are kernel proof rules, but
  source-level convenience theorems may still be useful when they improve
  tactic scripts
- congruence theorems for common constructors and prelude functions
- disequality theorems should generally be expressed as equality implying
  `absurd`

Symbol equality:

- `symbol_eq_true`
- `symbol_eq_false_distinct`
- `symbol_eq_refl`
- `symbol_eq_symm`
- `symbol_eq_computes_to_bool`
- `symbol_eq_true_implies_is_symbol_left`
- `symbol_eq_true_implies_is_symbol_right`

Value kind:

- `value_kind_symbol_implies_is_symbol`
- `value_kind_lambda_implies_is_lambda`
- `value_kind_list_implies_is_list`
- `is_symbol_true_implies_is_lambda_false`
- `is_symbol_true_implies_is_list_value_false`
- `is_lambda_true_implies_is_symbol_false`
- `is_lambda_true_implies_is_list_value_false`
- `is_list_value_true_implies_is_symbol_false`
- `is_list_value_true_implies_is_lambda_false`
- exactly-one-kind theorem for finalized values

Structural value equality:

- `value_eq_true_true`
- `value_eq_true_false`
- `value_eq_nil`
- `value_eq_nil_cons`
- `value_eq_cons_nil`
- `value_eq_cons`
- `value_eq_comparable_symbol`
- `value_eq_comparable_nil`
- `value_eq_comparable_cons`
- `value_eq_comparable_no_lambdas`
- `value_eq_true_implies_not_lambdas`
- `value_eq_true_implies_comparable_left`
- `value_eq_true_implies_comparable_right`
- `value_eq_sound`
- `value_eq_complete_for_comparable_values`
- `value_eq_refl`
- `value_eq_symm`
- `value_eq_trans`
- `value_eq_false_implies_not_equal_for_comparable_values`
- `value_eq_cons_true_elim`
- `value_eq_cons_false_cases`
- `cons_congr`
- `nil_not_cons`
- `symbol_not_list`
- `symbol_not_lambda`
- `list_not_lambda`

Equality and prelude functions:

- `append_congr`
- `reverse_congr`
- `map_congr`
- `filter_congr`
- `fold_right_congr`
- `fold_left_congr`
- `option_map_congr`
- `pair_congr`
- nat operation congruence for `succ`, `pred`, `add`, `sub`, `mul`, and
  comparisons
