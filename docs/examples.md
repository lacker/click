# Examples

End-to-end examples live in `mdtests/`. Prefer copying a nearby mdtest instead
of inventing syntax from memory.

## Basic Function Contracts

- `mdtests/scalar.md`: simplest scalar postcondition.
- `mdtests/argument_result.md`: relates argument and result.
- `mdtests/result_expression.md`: result expression support.
- `mdtests/default_prover.md`: omitted proof clauses use `auto`.
- `mdtests/simp_postconditions.md`: deterministic `simp` postconditions.

## Undefined Behavior And Arithmetic

- `mdtests/overflow.md`: signed overflow proof behavior.
- `mdtests/increment_requires_no_overflow.md`: requirement rules out overflow.
- `mdtests/increment_without_requires.md`: missing requirement fails.
- `mdtests/decrement_requires_no_underflow.md`: lower-bound arithmetic safety.

## Memory Safety And Postconditions

- `mdtests/pointer_range.md`: basic pointer valid range.
- `mdtests/pointer_range_missing_requires.md`: missing valid range fails.
- `mdtests/pointer_range_segment_syntax.md`: segment syntax.
- `mdtests/fill3_memory_postconditions.md`: post-state memory facts.
- `mdtests/fill3_bad_memory_postcondition.md`: failing memory postcondition.
- `mdtests/write_second_old_keeps_first.md`: old-value frame fact.
- `mdtests/write_second_old_rejects_overwritten_cell.md`: overwritten old-value
  rejection.

## Aliasing And Disjointness

- `mdtests/copy3_array_demo.md`: `valid_range`, `disjoint`, and old source
  values.
- `mdtests/pointer_params_may_alias_without_disjoint.md`: aliasing is allowed by
  default.
- `mdtests/disjoint_symbolic_unwritten_read.md`: symbolic disjointness.
- `mdtests/shifted_copy_effect_uses_covering_disjoint.md`: effect summary plus
  covering disjointness.

## Local Arrays

- `mdtests/local_array.md`: local array basics.
- `mdtests/local_array_loop.md`: bounded loop over a local array.
- `mdtests/local_array_loop_frame.md`: local array frame behavior.
- `mdtests/local_array_decays_to_helper.md`: array-to-pointer function call.
- `mdtests/local_array_rejects_assignment.md`: direct array assignment fails.

## Byte Values And Buffers

- `mdtests/uint8_literals.md`: `uint8` returns and ASCII character literals.
- `mdtests/uint8_buffer_read.md`: `uint8[]` parameter indexing with
  byte-sized `valid_range`.
- `mdtests/uint8_local_array.md`: local byte arrays and byte stores/loads.
- `mdtests/uint8_loop_invariant_pure_function.md`: `uint8[]` pure function
  calls inside loop invariants and `old(...)`.

## Loops And Invariants

- `mdtests/bounded_loop.md`: concrete bounded loop execution.
- `mdtests/count_to_three_loop_invariants.md`: loop invariants.
- `mdtests/count_to_n_loop_invariant.md`: symbolic loop bound.
- `mdtests/count_to_three_bad_invariant.md`: preservation failure.
- `mdtests/count_to_three_bad_invariant_initialization.md`: initialization
  failure.
- `mdtests/count_to_three_bad_assert.md`: assertion failure.
- `mdtests/fill_n_symbolic_pointer_loop.md`: symbolic pointer-loop safety.
- `mdtests/fill_n_segment_invariant.md`: quantified written-segment invariant.
- `mdtests/fill_tail_keeps_first.md`: old-value invariant.
- `mdtests/copy_n_segment_invariant.md`: copied segment invariant.

## Effects And Frames

- `mdtests/immutable_stack_locals.md`: stack-local writes under `immutable`.
- `mdtests/count_to_three_loop_immutable.md`: loop-level immutable clause.
- `mdtests/fill_n_mutable_segment.md`: symbolic mutable function segment.
- `mdtests/fill_n_loop_mutable_segment.md`: step-relative loop mutable segment.
- `mdtests/loop_frame_segment_shapes.md`: shifted, growing, and multi-segment
  loop effects.
- `mdtests/shifted_loop_effect_subset.md`: loop effect composes into function
  effect.
- `mdtests/shifted_loop_effect_preserves_prefix.md`: effect summary preserves
  prefix.

## Predicates And Pure Click Functions

- `mdtests/sorted_predicate.md`: named predicate and `unfold`.
- `mdtests/sorted_pair_unfold_requirement.md`: unfolding predicate requirement.
- `mdtests/opaque_predicate_requirement.md`: exact opaque predicate reuse.
- `mdtests/click_proposition_logic.md`: proposition syntax.
- `mdtests/forall_array_segment.md`: quantified array segment.
- `mdtests/forall_array_segment_rejects_overwritten_cell.md`: failing quantified
  old-memory proof.
- `mdtests/pure_click_functions.md`: `function`, `let`, `if`, `.fold`, `.all`,
  `.any`, stdlib `count`, and `permutation`.
- `mdtests/click_array_refs.md`: array refs carrying current and old memory into
  pure Click functions and predicates.
- `mdtests/byte_slice_stdlib.md`: stdlib byte-slice helpers over `uint8[]`,
  including byte counts, slice equality, range equality, and all-equal facts.
- `mdtests/byte_slice_range_predicates.md`: byte contains/all-not-equal
  predicates and `choose` after explicit predicate unfolding.

## Sorting And Permutation

- `mdtests/compare_swap2_sorted.md`: two-cell sorting.
- `mdtests/compare_swap2_sorted_predicate.md`: sorted predicate.
- `mdtests/compare_swap2_permutation.md`: stdlib `permutation` proof over a
  current array and `old(p)`.
- `mdtests/sort3_sorted.md`: three-cell sorting.
- `mdtests/sort3_permutation.md`: stdlib `permutation` proof for three-cell
  sorting.
- `mdtests/sort3_permutation_predicate.md`: explicit permutation packaged as a
  predicate.
- `mdtests/bubble_sort3_loop_sorted.md`: loop-shaped three-cell sorting.
- `mdtests/bubble_sort3_loop_permutation.md`: loop-shaped stdlib
  `permutation` proof using bounded execution.
- `mdtests/loop_stdlib_permutation_invariant.md`: stdlib `permutation` as a
  direct loop invariant using spec lowering for the `.fold` inside `count`.
- `mdtests/loop_old_count_invariant.md`: old-state stdlib `count` inside a loop
  invariant, exercising `old(...)` as entry-context spec elaboration.
- `mdtests/bubble_sort3_two_pass_sorted.md`: loop VCs for sortedness.
