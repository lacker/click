# Examples

Focused regression examples live in `mdtests/`. Each mdtest should be small and
self-contained, with inline C and `.click` blocks. Prefer copying a nearby
mdtest instead of inventing syntax from memory.

Larger example projects live directly under `examples/`. They contain ordinary
`.c` files and `.click` sidecars, and are verified by `tests/examples.rs`.

## Basic Function Contracts

- `mdtests/scalar.md`: simplest scalar postcondition.
- `mdtests/argument_result.md`: relates argument and result.
- `mdtests/result_expression.md`: result expression support.
- `mdtests/default_prover.md`: omitted proof clauses use `auto`.
- `mdtests/simp_postconditions.md`: deterministic `simp` postconditions.

## Pure Theorems

- `mdtests/pure_theorem.md`: theorem-only `.click` file with no C source.
- `mdtests/pure_theorem_unfold.md`: pure theorem proof script with predicate
  unfolding.
- `mdtests/pure_theorem_apply.md`: pure theorem proof script applying an
  earlier theorem.
- `mdtests/pure_theorem_rejects_execution_step.md`: theorem proofs reject C
  execution proof steps.
- `mdtests/theorem_apply_in_function_proof.md`: C function proof script applying
  a pure theorem after symbolic execution.
- `mdtests/theorem_apply_requires_precondition.md`: theorem application fails
  when the applied theorem's requirements are not available.

## Undefined Behavior And Arithmetic

- `mdtests/overflow.md`: signed overflow proof behavior.
- `mdtests/increment_requires_no_overflow.md`: requirement rules out overflow.
- `mdtests/increment_without_requires.md`: missing requirement fails.
- `mdtests/decrement_requires_no_underflow.md`: lower-bound arithmetic safety.
- `mdtests/c_multiplication.md`: signed multiplication in C fragments, pure
  Click expressions, precedence, and overflow behavior.
- `mdtests/c_division_remainder.md`: signed division and remainder in C
  fragments and pure Click expressions.
- `mdtests/c_division_by_zero.md`, `mdtests/c_remainder_by_zero.md`, and
  `mdtests/c_division_overflow.md`: division/remainder undefined behavior.
- `mdtests/c_bitwise.md`: `int32` bitwise operators in C fragments and pure
  Click expressions, plus `uint8` promotion through bitwise expressions.
- `mdtests/c_shifts.md`: signed `int32` shifts in C fragments and pure Click
  expressions, including arithmetic right shift.
- `mdtests/c_shift_negative_count.md`, `mdtests/c_shift_large_count.md`,
  `mdtests/c_shift_negative_left.md`, and `mdtests/c_shift_left_overflow.md`:
  shift undefined behavior.
- `mdtests/c_shift_uint8_promoted.md`: `uint8` promotion through shifts.
- `mdtests/c_statement_update_sugar.md`: standalone `++`, `--`, `+=`, `-=`,
  and `*=` statement sugar.
- `mdtests/c_statement_update_rejects_expression.md`: update expressions remain
  unsupported inside larger expressions.

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

## Structs

- `mdtests/struct_multifield_explicit_permissions.md`: compact multi-field
  struct loads/stores with explicit validity and write ranges.
- `mdtests/struct_field_resources_imply_validity.md`: preferred field-resource
  shape where `read(p->field)` and `write(p->field)` imply field validity.
- `mdtests/struct_pointer_field_explicit_permissions.md`: pointer-valued
  struct field load followed by a write through the loaded pointer, again using
  explicit ranges rather than ownership sugar.
- `mdtests/struct_symbolic_pointer_field_load.md`: a pointer-valued field is
  loaded from external memory and used as the base of a write resource.

## Byte Values And Buffers

- `mdtests/uint8_literals.md`: `uint8` returns and ASCII character literals.
- `mdtests/uint8_buffer_read.md`: `uint8[]` parameter indexing with
  byte-sized `valid_range`.
- `mdtests/uint8_local_array.md`: local byte arrays and byte stores/loads.
- `mdtests/uint8_narrowing.md`: checked `int32`-to-`uint8` narrowing with
  range requirements.
- `mdtests/uint8_narrowing_requires_range.md`: missing byte-range proof for
  narrowing fails.
- `mdtests/uint8_loop_invariant_pure_function.md`: `uint8[]` pure function
  calls inside loop invariants and `old(...)`.

## Loops And Invariants

- `mdtests/bounded_loop.md`: concrete bounded loop execution.
- `mdtests/c_for_loop.md`: assignment-style `for` loops lowered to `while`,
  including bounded execution and loop invariants.
- `mdtests/c_for_loop_rejects_declaration.md`: unsupported declaration-style
  `for` initializer.
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
- `mdtests/resource_context_write.md`: first `write(...)` resource-context
  example threaded through helper calls.
- `mdtests/resource_context_write_rejects_missing.md`: missing write resource
  diagnostic.
- `mdtests/resource_context_read.md`: first `read(...)` resource-context
  example.
- `mdtests/resource_context_read_rejects_write.md`: read permission does not
  permit stores.
- `mdtests/resource_context_write_implies_read.md`: write permission permits
  reads and satisfies read guarantees.
- `mdtests/resource_context_uint8_read.md`: read permission over `uint8[]`
  byte indexes.
- `mdtests/resource_context_uint8_write.md`: write permission over `uint8[]`
  byte indexes.
- `mdtests/resource_context_uint8_rejects_missing_read.md`: byte permission for
  one `uint8[]` element does not cover another.
- `mdtests/resource_summary_requires_returned_write.md`: helper call consumes a
  write resource unless its summary returns it.
- `mdtests/resource_summary_read_does_not_consume_write.md`: helper read
  requirement does not consume caller write permission.
- `mdtests/resource_summary_splits_write_range.md`: helper call receives a
  subrange while the caller keeps and rejoins the residue.
- `mdtests/resource_summary_splits_symbolic_write_range.md`: helper call
  receives and returns a symbolic write subrange.

The `permission_call_*` tests tell the same call-transfer story in a compact
sequence:

- `mdtests/permission_call_borrow_read.md`: a helper borrows read permission
  from a caller that keeps write permission.
- `mdtests/permission_call_consumes_write_without_return.md`: a helper consumes
  write permission when it does not return it.
- `mdtests/permission_call_returns_write.md`: a helper returns write permission
  to its caller.
- `mdtests/permission_call_split_rejoin.md`: a caller splits a write range for
  a helper call and rejoins it afterward.
- `mdtests/permission_free_not_write.md`: free permission does not grant write
  access.
- `mdtests/permission_free_consumes_access.md`: consuming free permission
  removes overlapping access permissions.
- `mdtests/permission_free_returns.md`: free permission can be returned through
  a helper summary.
- `mdtests/permission_free_split_rejoin.md`: free permission supports subrange
  split and rejoin.
- `mdtests/free_statement.md`: executable `free(p);` consumes free permission.
- `mdtests/free_statement_no_write_required.md`: `free(p);` does not require
  write permission.
- `mdtests/free_statement_write_after.md`: writing after `free(p);` fails.
- `mdtests/free_statement_double_free.md`: a second `free(p);` fails.
- `mdtests/affine_resource_borrow_return.md`: exact-match affine named
  resource can be borrowed and returned.
- `mdtests/affine_resource_consumed_by_call.md`: exact-match affine named
  resource is consumed when a callee does not return it.
- `mdtests/affine_resource_rejects_argument_type.md`: affine named resource
  arguments are checked against their declared types.
- `mdtests/affine_resource_rejects_duplicate.md`: duplicate affine named
  resource clauses are rejected.
- `mdtests/affine_resource_rejects_call_duplicate.md`: a call cannot satisfy
  two affine resource parameters with the same token.
- `mdtests/callback_resource_complete_once.md`: resource-only callback
  consumer can be called once.
- `mdtests/callback_resource_complete_twice.md`: affine callback token rejects
  double completion.
- `mdtests/callback_resource_branch_once.md`: branch-sensitive callback
  completion passes when each path completes once.
- `mdtests/callback_resource_branch_double.md`: branch-sensitive double
  completion fails on the path that spent the token.
- `mdtests/callback_resource_pipe_token.md`: a helper consumes one callback
  token while returning another.
- `mdtests/callback_resource_pipe_rejects_spent_token.md`: the caller cannot
  reuse the callback token spent by the helper.
- `mdtests/represented_resource_once_flag.md`: explicit `unpack(resource)` and
  `pack(resource)` steps verify an affine token represented by memory
  permission plus a fact.
- `mdtests/represented_resource_composes_named.md`: a represented resource can
  bundle another named affine resource with memory permission and a fact.
- `mdtests/represented_resource_two_arrays.md`: a represented resource can
  bundle permissions for multiple arrays.
- `mdtests/represented_resource_disjoint_fact.md`: a represented resource can
  package a `disjoint(...)` fact and expose it while unpacked.
- `mdtests/represented_resource_packed_pure_fact_projection.md`: a packed
  represented resource exposes pure facts while held.
- `mdtests/represented_resource_packed_memory_fact_projection.md`: a packed
  represented resource exposes memory facts while keeping contained permission
  hidden.
- `mdtests/represented_resource_packed_disjoint_fact_projection.md`: a packed
  represented resource exposes a packaged `disjoint(...)` fact.
- `mdtests/represented_resource_packed_fact_hides_permissions.md`: packed facts
  do not expose contained write permission.
- `mdtests/represented_resource_struct_owned_buffer.md`: a conservative
  struct-owned-buffer pattern with explicit owner and buffer parameters.
- `mdtests/represented_resource_owner_buffer_field_dependent.md`: the desired
  field-dependent owner-buffer shape, with the derived buffer permission and
  non-aliasing fact packaged inside the represented resource.
- `mdtests/represented_resource_rejects_bad_origin.md`: packing a represented
  resource fails when its fact has not been established.
- `mdtests/represented_resource_rejects_double_call.md`: a represented affine
  token is still consumed linearly through a call summary.
- `mdtests/represented_resource_rejects_duplicate_contains.md`: represented
  resources reject duplicate contained affine tokens.
- `mdtests/write_resources_imply_disjoint.md`: two visible `write(...)`
  resources imply a `disjoint(...)` fact without a separate requirement.
- `mdtests/write_resources_reject_proven_overlap.md`: provably overlapping
  visible `write(...)` resources are rejected.
- `mdtests/represented_resource_rejects_cycle.md`: represented-resource
  definitions reject containment cycles.
- `mdtests/represented_resource_pure_fact.md`: represented resources can carry
  scalar facts that do not read memory.
- `mdtests/represented_resource_symbolic_fact_coverage.md`: scalar fact bounds
  can justify indexed memory reads inside a contained write
  range.
- `mdtests/represented_resource_predicate_bounds_fact.md`: predicate-hidden
  scalar bounds can justify indexed memory reads inside a contained write range.
- `mdtests/represented_resource_rejects_missing_symbolic_bound.md`: symbolic
  coverage fails when a required bound is missing.
- `mdtests/represented_resource_rejects_unowned_fact_read.md`: facts
  cannot read memory without contained write permission.
- `mdtests/represented_resource_rejects_read_backed_fact.md`: contained
  read permission is not enough to stabilize a memory fact.
- `mdtests/represented_resource_rejects_predicate_hidden_fact_read.md`:
  predicate-hidden memory reads are checked against contained write permission.

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
- `mdtests/contract_let_bindings.md`: Rust-style `let name [: type] = value;`
  bindings in pure Click functions and function contracts.
- `mdtests/contract_let_where.md`: `let name: type where proposition;`
  witness bindings in function contracts.
- `mdtests/contract_let_type_mismatch.md`: explicit `let` type annotation
  mismatch diagnostic.
- `mdtests/byte_slice_stdlib.md`: stdlib byte-slice helpers over `uint8[]`,
  including byte counts, slice equality, range equality, and all-equal facts.
- `mdtests/byte_slice_range_predicates.md`: byte contains/all-not-equal
  predicates and `choose` after explicit predicate unfolding.
- `mdtests/cstr_stdlib.md`: first C-string predicates over `uint8[]`, including
  exact spec length, bounded terminator, and plain existential string facts.

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

## Example Projects

- `examples/jsonc-refcount/`: first library-shaped example project. It has
  ordinary C files and sidecar specs for a getter, setter, and increment helper
  over a one-field json-c-shaped object.

## Library-Shaped Mdtests

- `mdtests/jsonc_refcount_getter.md`: first json-c-shaped pilot proof,
  using a field read resource for a reference-count getter.
- `mdtests/jsonc_refcount_setter.md`: first-field struct write
  using a field write resource.
- `mdtests/jsonc_refcount_increment.md`: field read/modify/write
  proof with `old(obj->field)` postconditions and a no-overflow requirement.
