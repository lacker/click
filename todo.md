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

`if`:

- inversion theorems for true and false results with simple branch shapes

## Options

Core option encoding is currently covered by the `none`/`some` constructor
facts and by function-specific `*_computes_to_option` result-shape theorems.
Do not add a standalone `option_cases` theorem unless we first add an
`is-option` predicate; otherwise it is just the option-shape premise repeated
as its own conclusion.

Relationships with existing option-producing functions:

- `option_map_find`
- `option_bind_find`

## Pairs

Optional computational pair predicate:

- `is-pair` if we decide a computational predicate is useful

Pair theorems:

- `is_pair_pair`
- `is_pair_nil_false`
- `is_pair_singleton_false`
- `is_pair_cons_cons_nil_true`
- `is_pair_cons_cons_cons_false`

Relationships with existing pair-shaped APIs:

- `zip_pair_shape`
- `unzip_pair_shape`

## Lists

Length:

- `length_filter_le`
- `length_take`
- `length_drop`
- `length_take_add_length_drop`
- `length_zip_min`
- `length_concat`

Membership and indexing:

- `member_computes_to_bool`
- `member_append`
- `elem_index_append_left`
- `elem_index_append_right`

Take, drop, split-at:

- `drop_drop`
- `take_drop_commute`

Replication, zipping, and sequence helpers:

- `zip_unzip`
- `unzip_zip`
- `zip_with_as_map_zip`

## Natural Numbers

Representation and constructors:

- `nat_induction` as a source-level theorem if useful

Range:

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

- `symbol_eq_false_distinct`
- `symbol_eq_symm`
- `symbol_eq_computes_to_bool`
- `symbol_eq_true_implies_is_symbol_left`
- `symbol_eq_true_implies_is_symbol_right`

Structural value equality:

- `value_eq_cons_false_cases`

Equality and prelude functions:

- nat operation congruence for `succ`, `pred`, `add`, `sub`, `mul`, and
  comparisons
