# Proof landscape

This document tracks the proof capabilities Click should grow, how they relate
to familiar verification systems, and which mdtests currently exercise
them. It is a working design map, not a commitment that every tactic or axiom
will have exactly the names used here.

## Vocabulary

- An **axiom** is a built-in theorem-producing operation. In the literature,
  some of these would be called axiom schemas or trusted proof procedures, but
  Click uses the simpler word axiom.
- A **theorem** is a proposition produced by axioms.
- **Simple**, **smart**, and **control** tactics are defined in
  [Smart and simple tactics](smart-and-simple-tactics.md).
- A **pure proof** derives a proposition without a symbolic C state.
- A **fixed-state proof** reasons against one fixed symbolic C state. It has no
  execution frontier and cannot execute C. Of these proofs, only a
  result-aware outcome proof can fold and unfold logical resources.
- An **execution proof** establishes a pre/post relationship for a code region.
  It advances an execution frontier carrying symbolic state, pure facts, and
  resource facts. It may use pure and resource reasoning between execution
  steps.

See the [proof tactics reference](../reference/tactics/index.md) for the exhaustive current
classification, and its [core tactics](../reference/tactics/index.md#core-tactics)
for the ones a hand-written proof needs.

## Competitor families

Click should borrow ordinary ideas from existing systems rather than inventing
new proof workflow concepts too early.

- Interactive proof assistants: Lean, Coq, Isabelle.
  Relevant tactics include `close()`, `rewrite`, `cases`, `induction`,
  `specialize`, `exact`, `have`, and solver-backed automation.
- Auto-active verifiers: Dafny, F*, Why3.
  Relevant concepts include preconditions, postconditions, assertions,
  loop invariants, verification-condition generation, and solver discharge.
- C verification systems: Frama-C/WP with ACSL, VeriFast, VST, RefinedC.
  Relevant concepts include C memory models, function contracts, frame
  conditions, separation-style ownership, and loop invariants.
- Bounded and symbolic analyzers: CBMC, KLEE, SeaHorn.
  Relevant concepts include bounded execution, path splitting, overflow/undefined behavior
  checks, memory-safety checks, and counterexample-oriented diagnostics.

## Capability matrix

| Capability | Common source | Click axiom family | Click tactic surface | Current mdtest |
| --- | --- | --- | --- | --- |
| Scalar execution | symbolic evaluators, SMT-backed automation | C-fragment/statement execution | omitted proof (implicit tail), `step_until` | `mdtests/scalar.md`, `mdtests/argument_result.md`, `mdtests/max_symbolic.md` |
| C undefined behavior | CBMC, Frama-C/WP, UBSan-style checks | undefined behavior-aware C execution | omitted proof (implicit tail) diagnostics | `mdtests/overflow.md`, `mdtests/increment_requires_no_overflow.md`, `mdtests/increment_without_requires.md`, `mdtests/c_division_by_zero.md`, `mdtests/c_division_overflow.md`, `mdtests/c_shift_large_count.md`, `mdtests/c_shift_left_overflow.md` |
| Pointer viewability | C verifiers, separation logic | viewability and range axioms | omitted proof (implicit tail), `step_until` | `mdtests/pointer_range.md`, `mdtests/pointer_range_missing_requires.md`, `mdtests/fill_n_symbolic_pointer_loop.md` |
| Memory postconditions | ACSL/Dafny/F* function contracts | final-state memory evaluation | omitted proof, `close()` | `mdtests/fill3_memory_postconditions.md`, `mdtests/fill3_bad_memory_postcondition.md`, `mdtests/copy3_array_demo.md` |
| Bounded loops | bounded model checking, symbolic execution | budgeted repetition of ordinary execution steps | omitted proof (implicit tail), `step_until` | `mdtests/bounded_loop.md`, `mdtests/fill3.md`, `mdtests/fill3_array_loop.md` |
| Function calls | modular verification, inlining, call summaries | function environment and specification satisfaction | omitted proof (implicit tail), `step_until` | `mdtests/function_call.md` |
| Loop invariants | Dafny/F*/Why3/Frama-C | loop verification-condition generation for scalar locals, pointer safety, memory-changing invariants, and loop frames | `loop { invariant ...; initialize by ...; maintain by ...; }` at the execution frontier | `mdtests/count_to_n_loop_invariant.md`, `mdtests/c_for_loop.md`, `mdtests/fill_n_loop_mutable_segment.md`, `mdtests/copy_n_segment_invariant.md`, `mdtests/loop_stdlib_permutation_invariant.md` |
| Intermediate facts | Lean/Dafny/F* proof scripts | pure goals at the current execution frontier | `have ... by { ... }`, `close()`, `apply(fact)` | `mdtests/count_to_three_loop_invariants.md`, `mdtests/count_to_three_bad_assert.md` |
| Proposition syntax | Lean/Isabelle/Dafny/F* specifications | kernel `And`, `Or`, `Not`, `Implies`, `ForAll`, `Exists` propositions | `and`, `or`, `not`, `implies`, `forall`, `exists` | `mdtests/click_proposition_logic.md`, `mdtests/forall_array_segment.md`, `mdtests/forall_array_segment_rejects_overwritten_cell.md`, `mdtests/exists_and_symbolic_any.md` |
| Existential proof | Lean `exists`/`cases`, Coq `exists`/`destruct`, Dafny witnesses | proof-local existential introduction and elimination | `witness(expr)`, `let k = obtain(exists (x: T) { P });` | `mdtests/witness_and_choose.md` |
| Rewriting and simplification | Lean and Isabelle simplifiers | explicit equality substitution, structural conjunction elimination, named theorem rules, and simplification | `rewrite`, `have`, `normalize`, `close()` | `mdtests/simple_tactics.md`, `mdtests/solve_postconditions.md`, `mdtests/pure_click_functions.md` |
| Bitvector arithmetic | SMT, CBMC, hardware-oriented provers | bitvector32 solver/normalizer | omitted proof, `close()` | `mdtests/c_bitwise.md`, `mdtests/c_shifts.md`, `mdtests/c_shift_uint8_promoted.md` |
| Frame reasoning | separation logic, C verifiers | pre/post memory evaluation with symbolic initial cells and loop write footprints | omitted proof, contract `owns`/`views`, loop `owns` clauses | `mdtests/write_second_old_keeps_first.md`, `mdtests/write_second_old_rejects_overwritten_cell.md`, `mdtests/fill_n_loop_mutable_segment.md`, `mdtests/shifted_loop_effect_preserves_prefix.md` |
| C array and struct surface syntax | C frontends, C verifiers | parameter-array lowering, local stack blocks, LP64 struct field loads/stores, and retained struct-pointer field types | ordinary C/Click signatures plus explicit ranges for multi-field structs | `mdtests/fill3_array_loop.md`, `mdtests/copy3_array_demo.md`, `mdtests/local_array.md`, `mdtests/local_array_loop.md`, `mdtests/struct_multifield_explicit_permissions.md`, `mdtests/struct_pointer_field_explicit_permissions.md`, `mdtests/jsonc_refcount_getter.md`, `mdtests/jsonc_refcount_setter.md`, `mdtests/jsonc_refcount_increment.md` |
| Byte buffers | C string/memory libraries | `uint8` values, byte-width loads/stores, typed array refs | omitted proof, `close()`, `unfold` | `mdtests/uint8_literals.md`, `mdtests/uint8_buffer_read.md`, `mdtests/uint8_narrowing.md`, `mdtests/byte_count_of_two_merged_branches_matches_the_c_count.md`, `mdtests/cstr_stdlib.md` |
| Stdlib folds and permutation | functional array specs, multiset proofs | `RangeFold`, finite forall/range facts, count-shaped fold reasoning | `unfold`, `close()`, loop invariants | `mdtests/compare_swap2_permutation.md`, `mdtests/bubble_sort3_loop_permutation.md`, `mdtests/loop_stdlib_permutation_invariant.md` |
| Pure-function induction | Lean/Coq/Isabelle strong and structural induction | nonnegative `int32` or full-range `uint64` induction plus exhaustive constructor induction over recursive algebraic values, with exact local-hypothesis instantiation | `let ih = induct(value)`, `match xs { ... }`, `apply(ih(m))` | `mdtests/pure_induction_countdown.md`, `mdtests/uint64_measure_induction_counts_a_range_fold.md`, `mdtests/algebraic_structural_induction.md` |
