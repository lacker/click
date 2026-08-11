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
- A **simple tactic** is a deterministic, bounded tactic that performs one
  explicit proof step.
- A **proof** is a `by` clause containing a replayable tactic script or one
  smart tactic that can later be expanded into a simple-tactic certificate.
- A **smart tactic** may search or orchestrate several rules. Logically it
  should be replaceable by a sequence of simple tactics when it succeeds.
  Smart search is best-effort and incomplete; the simple tactic language, not
  automatic discovery, is the proof-expressivity boundary.
- A **control-flow tactic** creates proof scopes or subgoals in which other
  tactics run. Structurally, this includes `have`, proof-level `if`, `branch`,
  and `loop`. Timing and expansion additionally give the selectable `have` source
  occurrence the class of its supported body: SMART, SIMPLE, or CONTROL.
- A **pure proof** derives a proposition from facts at one execution point. It
  has no execution frontier and cannot execute C or transform resources.
- An **execution proof** establishes a pre/post relationship for a code region.
  It advances an execution frontier carrying symbolic state, pure facts, and
  resource facts. It may use pure and resource reasoning between execution
  steps.

See the [proof tactics reference](proof-tactics.md) for the exhaustive current
classification.

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
| Scalar execution | symbolic evaluators, SMT-backed automation | C-fragment/statement execution | `auto`, `execute()` | `mdtests/scalar.md`, `mdtests/argument_result.md`, `mdtests/max_symbolic.md` |
| C undefined behavior | CBMC, Frama-C/WP, UBSan-style checks | undefined behavior-aware C execution | `auto`, `execute()` diagnostics | `mdtests/overflow.md`, `mdtests/increment_requires_no_overflow.md`, `mdtests/increment_without_requires.md`, `mdtests/c_division_by_zero.md`, `mdtests/c_division_overflow.md`, `mdtests/c_shift_large_count.md`, `mdtests/c_shift_left_overflow.md` |
| Pointer loadability | C verifiers, separation logic | loadability and range axioms | `auto`, `execute()` | `mdtests/pointer_range.md`, `mdtests/pointer_range_missing_requires.md`, `mdtests/fill_n_symbolic_pointer_loop.md` |
| Memory postconditions | ACSL/Dafny/F* function contracts | final-state memory evaluation | `auto`, `simp()` | `mdtests/fill3_memory_postconditions.md`, `mdtests/fill3_bad_memory_postcondition.md`, `mdtests/copy3_array_demo.md` |
| Bounded loops | bounded model checking, symbolic execution | budgeted repetition of ordinary execution steps | `auto`, `execute()` | `mdtests/bounded_loop.md`, `mdtests/fill3.md`, `mdtests/fill3_array_loop.md` |
| Function calls | modular verification, inlining, call summaries | function environment and specification satisfaction | `auto`, `execute()` | `mdtests/function_call.md` |
| Loop invariants | Dafny/F*/Why3/Frama-C | loop verification-condition generation for scalar locals, pointer safety, memory-changing invariants, and loop frames | `loop { invariant ...; initialize by ...; preserve by ...; }` at the execution frontier | `mdtests/count_to_n_loop_invariant.md`, `mdtests/c_for_loop.md`, `mdtests/fill_n_loop_mutable_segment.md`, `mdtests/copy_n_segment_invariant.md`, `mdtests/loop_stdlib_permutation_invariant.md` |
| Intermediate facts | Lean/Dafny/F* proof scripts | pure goals at the current execution frontier | `have ... by { ... }`, `assumption`, `extract` | `mdtests/count_to_three_loop_invariants.md`, `mdtests/count_to_three_bad_assert.md` |
| Proposition syntax | Lean/Isabelle/Dafny/F* specifications | kernel `And`, `Or`, `Not`, `Implies`, `ForAll`, `Exists` propositions | `and`, `or`, `not`, `implies`, `forall`, `exists` | `mdtests/click_proposition_logic.md`, `mdtests/forall_array_segment.md`, `mdtests/forall_array_segment_rejects_overwritten_cell.md`, `mdtests/exists_and_symbolic_any.md` |
| Existential proof | Lean `exists`/`cases`, Coq `exists`/`destruct`, Dafny witnesses | proof-local existential introduction and elimination | `witness(k = expr)`, `choose(k from requirement N)` | `mdtests/witness_and_choose.md` |
| Rewriting and simplification | Lean `simp`, Isabelle simplifier | explicit equality substitution, structural conjunction elimination, named theorem rules, and simplification | `rewrite`, `extract`, `normalize`, `simp` | `mdtests/simple_tactics.md`, `mdtests/simp_postconditions.md`, `mdtests/pure_click_functions.md` |
| Bitvector arithmetic | SMT, CBMC, hardware-oriented provers | bitvector32 solver/normalizer | `auto`, `simp()` | `mdtests/c_bitwise.md`, `mdtests/c_shifts.md`, `mdtests/c_shift_uint8_promoted.md` |
| Frame reasoning | separation logic, C verifiers | pre/post memory evaluation with symbolic initial cells and loop write footprints | `auto`, `frame`, loop `mutable` / `step { mutable ... }` clauses | `mdtests/write_second_old_keeps_first.md`, `mdtests/write_second_old_rejects_overwritten_cell.md`, `mdtests/fill_n_loop_mutable_segment.md`, `mdtests/loop_frame_segment_shapes.md`, `mdtests/shifted_loop_effect_preserves_prefix.md` |
| C array and struct surface syntax | C frontends, C verifiers | parameter-array lowering, local stack blocks, LP64 struct field loads/stores, and retained struct-pointer field types | ordinary C/Click signatures plus explicit ranges for multi-field structs | `mdtests/fill3_array_loop.md`, `mdtests/copy3_array_demo.md`, `mdtests/local_array.md`, `mdtests/local_array_loop.md`, `mdtests/struct_multifield_explicit_permissions.md`, `mdtests/struct_pointer_field_explicit_permissions.md`, `mdtests/jsonc_refcount_getter.md`, `mdtests/jsonc_refcount_setter.md`, `mdtests/jsonc_refcount_increment.md` |
| Byte buffers | C string/memory libraries | `uint8` values, byte-width loads/stores, typed array refs | `auto`, `simp()`, `unfold` | `mdtests/uint8_literals.md`, `mdtests/uint8_buffer_read.md`, `mdtests/uint8_narrowing.md`, `mdtests/byte_slice_stdlib.md`, `mdtests/cstr_stdlib.md` |
| Stdlib folds and permutation | functional array specs, multiset proofs | `RangeFold`, finite forall/range facts, count-shaped fold reasoning | `unfold`, `simp`, loop invariants | `mdtests/compare_swap2_permutation.md`, `mdtests/sort3_permutation.md`, `mdtests/bubble_sort3_loop_permutation.md`, `mdtests/loop_stdlib_permutation_invariant.md` |
| Pure-function induction | Lean/Coq/Isabelle strong induction | nonnegative `int32` theorem induction with exact local-hypothesis instantiation | `induct(n) as ih`, `apply(ih(m))` | `mdtests/pure_induction_countdown.md`, `mdtests/pure_induction_two_step.md` |

## Current C0 Boundary

The current C0 subset is enough to make the first several categories
executable: scalar code, signed undefined behavior, bitwise and shift
operations, pointer range checks, bounded loops, known function calls, memory
postconditions, old-memory postconditions, C-style array-parameter syntax, local
arrays, byte buffers, and Click proposition syntax with `and`, `or`, `not`,
`implies`, `forall`, `exists`, `.all`, and `.any`.
`auto` can prove quantified array-segment postconditions, unchanged-memory
cases, frame facts outside loop write footprints, and several stdlib
fold/permutation facts. Region execution proofs support executable `assert`
propositions and loop `invariant` clauses, including memory-changing invariants
and invariants that unfold stdlib definitions such as `permutation`.

It is not yet enough for the full real-library proof story. The main missing
pieces are full struct values and aggregate types, heap allocation beyond the
fixed-size object slice, richer shared-ownership models, broader integer
types/conversions, theorem libraries beyond the first `apply(...)` slice,
richer intermediate fact
management, module/import support, and a real-C or pilot-driven frontend
strategy.

That is intentional. The mdtests should make the next missing piece obvious:
when a proof pattern needs a new C0 feature, add the feature because the proof
capability demands it, not because C has it.
