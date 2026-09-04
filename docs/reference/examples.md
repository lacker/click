# Examples

Focused regression examples live in `mdtests/`. Each mdtest should be small and
self-contained, with inline C and `.click` blocks. Prefer copying a nearby
mdtest instead of inventing syntax from memory.

Larger example projects live directly under `examples/`. They contain ordinary
`.c` files and `.click` sidecars, and are verified by `tests/examples.rs`.

`examples/heap-object/` is the focused allocation-lifetime project. It shows a
nullable factory, full initialization, a read-only borrower, ownership transfer
across calls, and destruction. The neighboring `heap_*` mdtests pin the main
negative cases: unresolved allocation outcome, uninitialized read, leak,
interior free, and double free.

`examples/runtime-int32-allocation/` is the focused runtime-sized array
allocation project. It proves `malloc(count * 4)` and matching `free` for a
positive signed-safe `int32` count. `examples/owned-vector/` composes that
lifetime support with a checked copy helper to verify ordinary
malloc-copy-install-free growth, including unchanged failure and live-prefix
preservation on success.

`examples/refcount/` verifies a heap object's resource-population lifecycle. Its
population body owns the allocation and object once, `count(object_ref(obj))`
tracks the stored reference count, and the project covers initialization,
retain, nonfinal release, final release, and free across opaque calls.

## Basic function contracts

- `mdtests/scalar.md`: simplest scalar postcondition.
- `mdtests/argument_result.md`: relates argument and result.
- `mdtests/result_expression.md`: result expression support.
- `mdtests/default_prover.md`: omitted proof clauses use `auto`.
- `mdtests/simp_postconditions.md`: deterministic `simp` postconditions.
- `mdtests/simp_equality_order_transport.md`: deterministic equality rewriting,
  discrete integer-bound normalization, and equality-linked arithmetic.
- `mdtests/tactic_execute.md`: explicit execution tactic `execute()`,
  the clearer name for whole-function symbolic execution from the current
  execution frontier.

## Pure theorems

- `mdtests/pure_theorem.md`: theorem-only `.click` file with no C source.
- `mdtests/pure_theorem_unfold.md`: pure theorem proof script with predicate
  unfolding.
- `mdtests/pure_theorem_apply.md`: pure theorem proof script applying an
  earlier theorem.
- `mdtests/condition_search_explicit_decomposition.md`: an explicit
  `simp() using` proof constrains smart condition search to named premises and
  expands to explicit rewrites.
- `mdtests/pure_theorem_rejects_execution_tactic.md`: theorem proofs reject C
  execution tactics.
- `mdtests/pure_theorem_rejects_observe_tactic.md`: theorem proofs reject
  resource fact-observation tactics.
- `mdtests/theorem_apply_in_function_proof.md`: execution proof applying a pure
  theorem after symbolic execution.
- `mdtests/theorem_apply_requires_precondition.md`: theorem application fails
  when the applied theorem's requirements are not available.

## Undefined behavior and arithmetic

- `mdtests/overflow.md`: signed overflow proof behavior.
- `mdtests/increment_requires_no_overflow.md`: requirement rules out overflow.
- `mdtests/increment_without_requires.md`: missing requirement fails.
- `mdtests/decrement_requires_no_underflow.md`: lower-bound arithmetic safety.
- `mdtests/pure_arithmetic_bounded_operations.md`: bounded products and
  constant remainder, shift, and bit-mask consequences.
- `mdtests/c_multiplication.md`: signed multiplication in C fragments, pure
  Click expressions, precedence, and overflow behavior.
- `mdtests/c_division_remainder.md`: signed division and remainder in C
  fragments and pure Click expressions.
- `mdtests/c_division_by_zero.md`, `mdtests/c_remainder_by_zero.md`, and
  `mdtests/c_division_overflow.md`: division/remainder undefined behavior.
- `mdtests/c_bitwise.md`: `int32` bitwise operators in C fragments and pure
  Click expressions, plus `uint8` promotion through bitwise expressions.
- `mdtests/xor_swap.md`: symbolic XOR normalization proves the three-step
  scalar `^=` swap against function-entry values.
- `mdtests/c_shifts.md`: signed `int32` shifts in C fragments and pure Click
  expressions, including arithmetic right shift.
- `mdtests/c_shift_negative_count.md`, `mdtests/c_shift_large_count.md`,
  `mdtests/c_shift_negative_left.md`, and `mdtests/c_shift_left_overflow.md`:
  shift undefined behavior.
- `mdtests/c_shift_uint8_promoted.md`: `uint8` promotion through shifts.
- `mdtests/c_statement_update_sugar.md`: standalone `++`, `--`, `+=`, `-=`,
  and `*=` statement sugar; `mdtests/xor_swap.md` exercises `^=`.
- `mdtests/c_statement_update_rejects_expression.md`: update expressions remain
  unsupported inside larger expressions.
- `mdtests/infinite_loop_partial_contract.md`: a perpetual loop still proves
  finite-prefix safety without a termination claim.
- `mdtests/infinite_loop_vacuous_ensure.md`: a postcondition is vacuous when a
  perpetual function has no returning execution.

## Memory safety and postconditions

- `mdtests/pointer_range.md`: basic pointer loadability.
- `mdtests/pointer_range_missing_requires.md`: missing loadable range fails.
- `mdtests/pointer_range_segment_syntax.md`: segment syntax.
- `mdtests/fill3_memory_postconditions.md`: post-state memory facts.
- `mdtests/fill3_bad_memory_postcondition.md`: failing memory postcondition.
- `mdtests/write_second_old_keeps_first.md`: old-value frame fact.
- `mdtests/write_second_old_rejects_overwritten_cell.md`: overwritten old-value
  rejection.
- `mdtests/malloc_pointer_arrays.md`: heap allocation, pointer-cell stores and
  loads, and complete `free` for `int32**` and `uint8**`.
- `mdtests/malloc_pointer_array_bounds.md`: one-past pointer-array access is
  rejected without authorization.
- `mdtests/heap_pointer_array_uninitialized.md`: fresh pointer-array cells
  cannot be read before they are initialized.
- `mdtests/calloc_pointer_arrays.md`: zero-initialized pointer-array cells and
  complete reclamation.
- `mdtests/calloc_pointer_array_null_deref.md`: null pointer-array cells remain
  invalid to dereference.
- `mdtests/realloc_pointer_arrays.md`: pointer-array prefix preservation across
  growth and shrink.
- `mdtests/realloc_calloc_pointer_arrays.md`: zeroed pointer-array prefix
  preservation and writable growth tails.
- `mdtests/realloc_calloc_pointer_array_tail_is_uninitialized.md`: grown
  zeroed pointer-array tails remain uninitialized.

## Aliasing and separation

- `mdtests/copy3_array_demo.md`: `loadable`, `separate(memory(...))`, and old source
  values.
- `mdtests/pointer_params_may_alias_without_separate.md`: aliasing is allowed by
  default.
- `mdtests/separate_symbolic_unwritten_read.md`: symbolic memory separation.
- `mdtests/shifted_copy_effect_uses_covering_separate.md`: effect summary plus
  covering separation.

## Local arrays

- `mdtests/local_array.md`: local array basics.
- `mdtests/local_array_loop.md`: bounded loop over a local array.
- `mdtests/local_array_loop_frame.md`: local array frame behavior.
- `mdtests/local_array_decays_to_helper.md`: array-to-pointer function call.
- `mdtests/local_array_rejects_assignment.md`: direct array assignment fails.

## Structs

- `mdtests/struct_multifield_explicit_permissions.md`: compact multi-field
  struct loads/stores with explicit loadability and write ranges.
- `mdtests/struct_field_resources_imply_loadability.md`: preferred field-resource
  shape where viewed and owned field resources imply field loadability.
- `mdtests/struct_pointer_field_explicit_permissions.md`: pointer-valued
  struct field load followed by a write through the loaded pointer, again using
  explicit ranges rather than ownership sugar.
- `mdtests/struct_symbolic_pointer_field_load.md`: a pointer-valued field is
  loaded from external memory and used as the base of a write resource.
- `mdtests/struct_array_parameter_fields.md`: a one-dimensional struct array
  parameter retains the ABI stride for indexed field loads and stores.
- `mdtests/struct_by_value_embedded_copy.md`: by-value structs recursively copy
  fields from an embedded struct into fresh address-backed storage.
- `mdtests/struct_by_value_pointer_copy.md`: by-value structs shallow-copy data
  pointers while keeping ordinary-field updates isolated.
- `mdtests/struct_multidimensional_embedded_array.md`: a fixed multidimensional
  array of embedded structs preserves row-major indexing and ABI element stride.

## Byte values and buffers

- `mdtests/uint8_literals.md`: `uint8` returns and ASCII character literals.
- `mdtests/uint8_buffer_read.md`: `uint8[]` parameter indexing with
  byte-sized `loadable`.
- `mdtests/uint8_local_array.md`: local byte arrays and byte stores/loads.
- `mdtests/uint8_narrowing.md`: checked `int32`-to-`uint8` narrowing with
  range requirements.
- `mdtests/uint8_narrowing_requires_range.md`: missing byte-range proof for
  narrowing fails.
- `mdtests/uint8_widening.md`: `uint8` values widen through `int32` assignments
  and returns.
- `mdtests/uint8_loop_invariant_pure_function.md`: `uint8[]` pure function
  calls inside loop invariants and `old(...)`.
- `mdtests/uint32_arithmetic.md`: scalar `uint32` aliases, modular addition and
  subtraction, and unsigned ordered comparisons.
- `mdtests/uint32_operators.md`: scalar `uint32` multiplication, division,
  remainder, bitwise operators, shifts, unary negation, and update assignments.
- `mdtests/uint32_division_by_zero.md` and `mdtests/uint32_invalid_shift.md`:
  unsigned operator undefined-behavior diagnostics.

## Loops and invariants

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
- `mdtests/loop_preserve_branch.md`: explicit branch-aware preservation of a
  loop invariant through one arbitrary iteration.
- `mdtests/later_loop_preserve.md`: forward structural traversal reaches an
  explicit preservation proof on a later loop.
- `mdtests/nested_loop_preserve.md`: a nested loop preservation proof starts
  from its enclosing arbitrary-iteration frontier.
- `mdtests/count_to_three_bad_assert.md`: assertion failure.
- `mdtests/fill_n_symbolic_pointer_loop.md`: symbolic pointer-loop safety.
- `mdtests/fill_n_segment_invariant.md`: quantified written-segment invariant.
- `mdtests/fill_tail_keeps_first.md`: old-value invariant.
- `mdtests/copy_n_segment_invariant.md`: copied segment invariant.

## Effects and frames

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
- `mdtests/resource_context_write.md`: first owned-memory resource-context
  example threaded through helper calls.
- `mdtests/resource_context_write_rejects_missing.md`: missing write resource
  diagnostic.
- `mdtests/resource_context_read.md`: first viewed-memory resource-context
  example.
- `mdtests/read_permission_stable_repeated_load.md`: read permission gives a
  stable repeated-load view when no write intervenes.
- `mdtests/resource_context_read_rejects_write.md`: read permission does not
  permit stores.
- `mdtests/resource_context_write_implies_read.md`: write permission permits
  reads and satisfies read guarantees.
- `mdtests/write_permission_has_read_core.md`: write permission carries the
  same stable read core view as read permission.
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
- `mdtests/token_resource_borrow_return.md`: exact-match token
  resource can be borrowed and returned.
- `mdtests/token_resource_consumed_by_call.md`: exact-match token
  resource is consumed when a callee does not return it.
- `mdtests/token_resource_rejects_argument_type.md`: token resource
  arguments are checked against their declared types.
- `mdtests/token_resource_rejects_duplicate.md`: duplicate owned token
  resource clauses are rejected.
- `mdtests/token_resource_rejects_call_duplicate.md`: a call cannot satisfy
  two resource parameters with the same token.
- `mdtests/callback_resource_complete_once.md`: resource-only callback
  consumer can be called once.
- `mdtests/callback_resource_complete_twice.md`: callback resource rejects
  double completion.
- `mdtests/callback_resource_branch_once.md`: branch-sensitive callback
  completion passes when each path completes once.
- `mdtests/callback_resource_branch_double.md`: branch-sensitive double
  completion fails on the path that spent the token.
- `mdtests/callback_resource_pipe_token.md`: a helper consumes one callback
  token while returning another.
- `mdtests/callback_resource_pipe_rejects_spent_token.md`: the caller cannot
  reuse the callback token spent by the helper.
- `mdtests/composite_resource_once_flag.md`: explicit `unfold(resource)` and
  `fold(resource)` steps verify a resource token backed by memory
  permission plus a fact.
- `mdtests/composite_resource_composes_token.md`: a composite resource can
  bundle another token resource with memory permission and a fact.
- `mdtests/counted_resource_transfer.md`: two equal resource capabilities
  normalize to a quantity and are consumed by separate opaque calls one unit
  at a time.
- `mdtests/counted_resource_rejects_minting.md`: a contract cannot turn one
  resource unit into two without preserving its population body.
- `mdtests/counted_resource_rejects_double_spend.md`: one resource unit cannot
  satisfy two consuming calls.
- `mdtests/proof_branch_composite_resource_transform.md`: different branch
  token transformations fold and export one composite resource through an
  `ensuring` interface, then `observe` recovers its fact after the join.
- `mdtests/proof_branch_pointer_local.md`: selects a pointer in separate
  branches, exports its viewed range through a branch interface, and
  transports the selected value to the result after the join.
- `mdtests/proof_branch_owned_pointer_local.md`: exports ownership of a
  branch-selected pointer, mutates it after the join, and reads back the write.
- `mdtests/composite_resource_two_arrays.md`: a composite resource can
  bundle memory resources for multiple arrays.
- `mdtests/composite_resource_separate_fact.md`: a composite resource can
  package a `separate(...)` fact and expose it while unfolded.
- `mdtests/composite_resource_folded_pure_fact_projection.md`: a folded
  composite resource exposes pure facts while held.
- `mdtests/composite_resource_folded_memory_fact_projection.md`: a folded
  composite resource exposes memory facts while keeping the contained memory resource
  hidden.
- `mdtests/composite_resource_folded_separate_fact_projection.md`: a folded
  composite resource exposes a packaged `separate(...)` fact.
- `mdtests/composite_resource_folded_nested_fact_projection.md`: a folded
  composite resource does not recursively expose nested facts without
  observation.
- `mdtests/composite_resource_folded_fact_hides_permissions.md`: folded facts
  do not expose contained write permission.
- `mdtests/composite_resource_observe_nested_fact.md`: `observe(resource)`
  exposes one view layer, so nested facts require repeated observation.
- `mdtests/composite_resource_observe_hides_permissions.md`: `observe(...)`
  does not expose contained write permission.
- `mdtests/composite_resource_struct_owned_buffer.md`: a conservative
  struct-owned-buffer pattern with explicit owner and buffer parameters.
- `mdtests/composite_resource_owner_buffer_field_dependent.md`: the desired
  field-dependent owner-buffer shape, with the derived buffer resource and
  non-aliasing fact packaged inside the composite resource.
- `mdtests/composite_resource_owned_buffer_len_cap_data.md`: a len/cap/data
  owned-buffer resource with a stronger "has room" pre-state resource that
  folds back to the ordinary well-formed buffer after push.
- `mdtests/composite_resource_owned_buffer_observe_len.md`: a len/cap/data
  owned-buffer getter that uses `observe(...)` to read through the folded
  resource without unfolding owned contained resources.
- `mdtests/composite_resource_owned_buffer_get.md`: first-cell backing-buffer
  read through a len/cap/data owned-buffer resource.
- `mdtests/composite_resource_owned_buffer_observe_indexed.md`:
  field-dependent indexed backing-array read with only `observe(...)`.
- `mdtests/composite_resource_owned_buffer_set.md`: first-cell backing-buffer
  mutation that unfolds and folds the owned composite resource.
- `mdtests/composite_resource_owned_buffer_clear.md`: field mutation that
  restores the same owned composite resource after clearing `len`.
- `mdtests/composite_resource_execute_until_direct_mutate.md`: first passing
  execution proof, pausing before a direct mutation so the composite
  resource can be unfolded at the mutation point.
- `mdtests/composite_resource_step_direct_mutate.md`: statement-level
  execution proof, using `step()` to interleave execution with
  `observe`, `unfold`, and `fold`.
- `mdtests/composite_resource_view_then_mutate.md`: caller observes an owned
  composite before a view-only helper call, then unfolds before a later owned
  mutation. The helper call transfers the folded view through its verified
  contract without exposing contained resources to the caller.
- `mdtests/opaque_function_contract_call.md`: a mutating helper call executes
  as one step and exposes only its verified resource and memory postconditions.
- `mdtests/opaque_call_requires_verified_rule.md`: expected-fail coverage for a
  caller that appears before its callee's verified rule is available.
- `mdtests/opaque_call_rejects_weak_postcondition.md`: expected-fail coverage
  showing that an opaque caller cannot use an implementation write omitted
  from the callee contract.
- `mdtests/opaque_call_old_entry_state.md`: a callee's `old(...)` postcondition
  is instantiated at the call-entry memory snapshot.
- `mdtests/modular_pointer_postcondition.md`: a pointer-valued postcondition
  becomes an explicit caller pure fact after a verified modular call.
- `mdtests/opaque_resource_proposition_contract.md`: `separate(...)`,
  `contains(...)`, and `loadable(...)` cross an opaque call as ordinary
  state-indexed propositions.
- `mdtests/composite_resource_observe_nested_separate_contains.md`: explicit
  chained observation exposes `contains(...)` and `separate(...)` facts for a
  nested composite resource.
- `mdtests/composite_resource_nested_observe_not_automatic.md`: expected-fail
  coverage for the deliberate boundary where `auto` does not recursively
  observe nested composite resources.
- `mdtests/composite_resource_owner_buffer_hidden_separate_projection.md`:
  hidden contained writes imply folded-resource `separate(...)` facts without
  exposing the hidden owned memory resources.
- `mdtests/composite_resource_rejects_bad_origin.md`: folding a composite
  resource fails when its fact has not been established.
- `mdtests/composite_resource_rejects_double_call.md`: a composite
  resource owned once cannot satisfy two consuming calls through a call
  summary.
- `mdtests/composite_resource_rejects_duplicate_contains.md`: repeated
  contained resource clauses form the corresponding quantity.
- `mdtests/write_resources_imply_separate.md`: two visible owned-memory
  resources imply a `separate(...)` fact without a separate requirement.
- `mdtests/write_resources_reject_proven_overlap.md`: provably overlapping
  visible owned-memory resources are rejected.
- `mdtests/composite_resource_rejects_cycle.md`: composite-resource
  definitions reject containment cycles.
- `mdtests/conditional_resource_body.md`: a load-free condition selects either
  one composite body or the empty body.
- `mdtests/conditional_resource_guard_must_be_load_free.md`: resource guards
  cannot read memory.
- `mdtests/conditional_resource_unfold_requires_decided_guard.md`: explicit
  unfolding rejects an unknown guard instead of guessing a body.
- `mdtests/recursive_conditional_resource.md`: guarded direct self-recursion
  unfolds one node while leaving the recursive tail folded.
- `mdtests/recursive_resource_requires_guard.md`: unguarded direct recursion
  remains rejected.
- `mdtests/recursive_resource_rejects_mutual_cycle.md`: guarded mutual
  recursion remains rejected.
- `mdtests/composite_resource_pure_fact.md`: composite resources can carry
  scalar facts that do not read memory.
- `mdtests/composite_resource_symbolic_fact_coverage.md`: scalar fact bounds
  can justify indexed memory reads inside a contained write
  range.
- `mdtests/composite_resource_predicate_bounds_fact.md`: predicate-hidden
  scalar bounds can justify indexed memory reads inside a contained write range.
- `mdtests/composite_resource_rejects_missing_symbolic_bound.md`: symbolic
  coverage fails when a required bound is missing.
- `mdtests/composite_resource_rejects_unowned_fact_read.md`: facts
  cannot read memory without contained write permission.
- `mdtests/composite_resource_rejects_read_backed_fact.md`: contained
  read permission is not enough to stabilize a memory fact.
- `mdtests/composite_resource_rejects_predicate_hidden_fact_read.md`:
  predicate-hidden memory reads are checked against contained write permission.

## Predicates and pure Click functions

- `mdtests/sorted_predicate.md`: named predicate and `unfold`.
- `mdtests/memory_predicate_explicit_frame.md`: explicit frame proof for a
  memory-dependent predicate across a separate store.
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

## Sorting and permutation

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

## Example projects

- `examples/input-cursor/`: nested composite resources with independently
  mutable cursors sharing one viewed backing input.
- `examples/jsonc-refcount/`: synthetic library-shaped example project. It has
  ordinary C files and sidecar specs for a getter, setter, and increment helper
  over a one-field json-c-shaped object; it is not unchanged json-c source.
- `examples/jsonc-existing-source/`: byte-preserved upstream json-c source
  with a checked SHA-256 manifest. The examples gate reports its current
  parser-only qualification until the linked C0 frontend gaps close.
- `examples/detachable-buffer/`: attached metadata and storage split into two
  independently owned resources and later recombined.
- `examples/borrowed-slice/`: a symbolic middle range leaves its owner as an
  independent resource while metadata, prefix, and suffix remain owned by the
  enclosing buffer state.
- `examples/ring-buffer/`: linear and wrapped logical states retain the same
  nested full-backing ownership behind an owner-only API.
- `examples/linked-list/`: a guarded recursive resource over preallocated
  singly linked nodes, with one-layer push/pop proofs and a modular round trip.
- `examples/allocated-linked-list/`: fixed-size heap allocation packaged in a
  recursive list resource, including allocation-failure preservation,
  one-layer free, and a terminating recursive destructor.
- `examples/binary-tree/`: a guarded recursive resource with two owned child
  trees, including construction, child swapping, a modular leaf pipeline, and
  an immutable recursive walk that visits both sibling subtrees.
- `examples/recursive-zero-list/`: read-only recursive C traversal over a
  guarded list resource, with both structural-resource and numeric termination
  proofs kept separate from its ordinary partial contract.
- `examples/owned-vector/`: composite-resource example over vector metadata and
  dependent backing storage, including viewed reads, runtime-sized allocation,
  malloc-copy-free growth, and a resource-neutral in-capacity push shared by
  caller-supplied and allocation-owning vectors.
- `examples/owned-string/`: composite-resource example over string metadata and
  storage with a trailing terminator, including content-invariant preservation
  and a precise field-derived push footprint used by a modular caller.
- `examples/owned-split-buffer/`: composite resource with two adjacent sibling
  ranges, independent left/right mutation, and ownership repartitioning when
  their shared boundary moves.
- `examples/owned-segmented-buffer/`: nested owned composite resources with
  independent child mutation, logical concatenation reads, and metadata-only
  permutation of the two child resources.

## Library-shaped mdtests

- `mdtests/jsonc_refcount_getter.md`: first json-c-shaped pilot proof,
  using a viewed field resource for a reference-count getter.
- `mdtests/jsonc_refcount_setter.md`: first-field struct write
  using an owned field resource.
- `mdtests/jsonc_refcount_increment.md`: field read/modify/write
  proof with `old(obj->field)` postconditions and a no-overflow requirement.
