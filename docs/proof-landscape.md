# Proof Landscape

This document tracks the proof capabilities Click should grow, how they relate
to familiar verification systems, and which mdtests currently exercise
them. It is a working design map, not a commitment that every tactic or axiom
will have exactly the names used here.

## Vocabulary

- An **axiom** is a built-in theorem-producing operation. In the literature,
  some of these would be called axiom schemas or trusted proof procedures, but
  Click uses the simpler word axiom.
- A **theorem** is a proposition produced by axioms.
- A **proof step** is a deterministic proof-language call that invokes an axiom
  or a fixed deterministic sequence of axioms.
- A **proof** is a `by` clause: either a replayable sequence of proof steps, or
  a tactic call that can later be expanded into proof steps.
- A **tactic** is a heuristic program that tries to generate a proof. Tactics may
  search; proof steps should be stable and replayable.

The current `.click` language exposes function-level `requires` clauses and
per-guarantee `ensures ... by auto;` clauses, backed by native C symbolic
execution and specification-checking axioms in the kernel. Surface Click
may contain **C fragments**: pieces of C0 syntax that keep C-like local syntax
and typing but elaborate into explicit Kernel Click.

## Competitor Families

Click should borrow ordinary ideas from existing systems rather than inventing
new proof workflow concepts too early.

- Interactive proof assistants: Lean, Coq, Isabelle.
  Relevant tactics include `simp`, `rewrite`, `cases`, `induction`,
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

## Capability Matrix

| Capability | Common source | Click axiom family | Click tactic surface | Current mdtest |
| --- | --- | --- | --- | --- |
| Scalar execution | symbolic evaluators, SMT-backed automation | C-fragment/statement execution | `auto`, `symbolic_execute()` | `mdtests/scalar.md`, `mdtests/argument_result.md`, `mdtests/max_symbolic.md` |
| C undefined behavior | CBMC, Frama-C/WP, UBSan-style checks | undefined behavior-aware C execution | `auto`, `symbolic_execute()` diagnostics | `mdtests/overflow.md`, `mdtests/increment_requires_no_overflow.md`, `mdtests/increment_without_requires.md`, `mdtests/c_division_by_zero.md`, `mdtests/c_division_overflow.md`, `mdtests/c_shift_large_count.md`, `mdtests/c_shift_left_overflow.md` |
| Pointer range safety | C verifiers, separation logic | memory-validity and range axioms | `auto`, `symbolic_execute()` | `mdtests/pointer_range.md`, `mdtests/pointer_range_missing_requires.md`, `mdtests/fill_n_symbolic_pointer_loop.md` |
| Memory postconditions | ACSL/Dafny/F* function contracts | final-state memory evaluation | `auto`, `simp()` | `mdtests/fill3_memory_postconditions.md`, `mdtests/fill3_bad_memory_postcondition.md`, `mdtests/copy3_array_demo.md` |
| Bounded loops | bounded model checking, symbolic execution | budgeted loop execution | `auto`, `bounded_execute()` | `mdtests/bounded_loop.md`, `mdtests/fill3.md`, `mdtests/fill3_array_loop.md` |
| Function calls | modular verification, inlining, call summaries | function environment and specification satisfaction | `auto`, `symbolic_execute()` | `mdtests/function_call.md` |
| Loop invariants | Dafny/F*/Why3/Frama-C | loop verification-condition generation for scalar locals, pointer safety, memory-changing invariants, and loop frames | `loop N { invariant ... }`, `loop_vc(loop N)` | `mdtests/count_to_three_loop_invariants.md`, `mdtests/count_to_n_loop_invariant.md`, `mdtests/fill_n_symbolic_pointer_loop.md`, `mdtests/fill_n_segment_invariant.md`, `mdtests/copy_n_segment_invariant.md`, `mdtests/loop_stdlib_permutation_invariant.md` |
| Assertions and facts | Lean/Dafny/F* proof scripts | ghost assertion checking | `statement N { assert ... by auto; }`, later `have`, `exact` | `mdtests/count_to_three_loop_invariants.md`, `mdtests/count_to_three_bad_assert.md` |
| Proposition syntax | Lean/Isabelle/Dafny/F* specifications | kernel `And`, `Or`, `Not`, `Implies`, `ForAll`, `Exists` propositions | `and`, `or`, `not`, `implies`, `forall`, `exists` | `mdtests/click_proposition_logic.md`, `mdtests/forall_array_segment.md`, `mdtests/forall_array_segment_rejects_overwritten_cell.md`, `mdtests/exists_and_symbolic_any.md` |
| Existential proof | Lean `exists`/`cases`, Coq `exists`/`destruct`, Dafny witnesses | proof-local existential introduction and elimination | `witness(k = expr)`, `choose(k from requirement N)` | `mdtests/witness_and_choose.md` |
| Rewriting and simplification | Lean `simp`, Isabelle simplifier | rewrite theorem application | `simp`, later `rewrite`, `calc` | `mdtests/simp_postconditions.md`, `mdtests/pure_click_functions.md` |
| Bitvector arithmetic | SMT, CBMC, hardware-oriented provers | bitvector32 solver/normalizer | `auto`, `simp()` | `mdtests/c_bitwise.md`, `mdtests/c_shifts.md`, `mdtests/c_shift_uint8_promoted.md` |
| Frame reasoning | separation logic, C verifiers | pre/post memory evaluation with symbolic initial cells and loop write footprints | `auto`, `frame`, `frame(loop N)` | `mdtests/write_second_old_keeps_first.md`, `mdtests/write_second_old_rejects_overwritten_cell.md`, `mdtests/fill_tail_keeps_first.md`, `mdtests/loop_frame_segment_shapes.md`, `mdtests/shifted_loop_effect_preserves_prefix.md` |
| C array and pilot struct surface syntax | C frontends, C verifiers | parameter-array lowering, local stack blocks, and first-field struct getter lowering | ordinary C/Click signatures | `mdtests/fill3_array_loop.md`, `mdtests/copy3_array_demo.md`, `mdtests/local_array.md`, `mdtests/local_array_loop.md`, `mdtests/jsonc_mini_ref_count_getter.md` |
| Byte buffers | C string/memory libraries | `uint8` values, byte-width loads/stores, typed array refs | `auto`, `simp()`, `unfold` | `mdtests/uint8_literals.md`, `mdtests/uint8_buffer_read.md`, `mdtests/uint8_narrowing.md`, `mdtests/byte_slice_stdlib.md`, `mdtests/cstr_stdlib.md` |
| Stdlib folds and permutation | functional array specs, multiset proofs | `RangeFold`, finite forall/range facts, count-shaped fold reasoning | `unfold`, `simp`, `loop_vc(loop N)` | `mdtests/compare_swap2_permutation.md`, `mdtests/sort3_permutation.md`, `mdtests/bubble_sort3_loop_permutation.md`, `mdtests/loop_stdlib_permutation_invariant.md` |

## Current C0 Boundary

The current C0 subset is enough to make the first several categories
executable: scalar code, signed undefined behavior, bitwise and shift
operations, pointer range checks, bounded loops, known function calls, memory
postconditions, old-memory postconditions, C-style array-parameter syntax, local
arrays, byte buffers, and Click proposition syntax with `and`, `or`, `not`,
`implies`, `forall`, `exists`, `.all`, and `.any`.
`auto` can prove quantified array-segment postconditions, unchanged-memory
cases, frame facts outside loop write footprints, and several stdlib
fold/permutation facts. Structural proof blocks support executable `assert`
propositions and loop `invariant` clauses, including memory-changing invariants
and invariants that unfold stdlib definitions such as `permutation`.

It is not yet enough for the full real-library proof story. The main missing
pieces are full structs/layout, heap allocation and ownership, broader integer
types/conversions, reusable lemma declarations, richer intermediate fact
management, module/import support, and a real-C or pilot-driven frontend
strategy.

That is intentional. The mdtests should make the next missing piece obvious:
when a proof pattern needs a new C0 feature, add the feature because the proof
capability demands it, not because C has it.
