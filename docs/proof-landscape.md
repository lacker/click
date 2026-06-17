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
execution and specification-checking axioms in the megakernel.

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
| Scalar execution | symbolic evaluators, SMT-backed automation | C expression/statement execution | `auto`, later `symbolic_execute` | `mdtests/scalar.md`, `mdtests/argument_result.md`, `mdtests/max_symbolic.md` |
| C undefined behavior | CBMC, Frama-C/WP, UBSan-style checks | undefined behavior-aware C execution | `auto`, later `check_undefined_behavior` or verification-condition output | `mdtests/overflow.md`, `mdtests/increment_requires_no_overflow.md`, `mdtests/increment_without_requires.md` |
| Pointer range safety | C verifiers, separation logic | memory-validity and range axioms | `auto`, later `bounds` or `frame` | `mdtests/pointer_range.md`, `mdtests/pointer_range_missing_requires.md`, `mdtests/fill_n_symbolic_pointer_loop.md` |
| Memory postconditions | ACSL/Dafny/F* function contracts | final-state memory evaluation | `auto`, later `frame` | `mdtests/fill3_memory_postconditions.md`, `mdtests/fill3_bad_memory_postcondition.md`, `mdtests/copy3_array_demo.md` |
| Bounded loops | bounded model checking, symbolic execution | budgeted loop execution | `auto`, later `bounded_check` | `mdtests/bounded_loop.md`, `mdtests/fill3.md`, `mdtests/fill3_array_loop.md` |
| Function calls | modular verification, inlining, call summaries | function environment and specification satisfaction | `auto`, later `use specification` | `mdtests/function_call.md` |
| Loop invariants | Dafny/F*/Why3/Frama-C | loop verification-condition generation for scalar locals, pointer safety, and first write-footprint frames | `at loop N { invariant ... by auto; }` | `mdtests/count_to_three_at_loop_invariants.md`, `mdtests/count_to_n_loop_invariant.md`, `mdtests/fill_n_symbolic_pointer_loop.md`, `mdtests/fill_tail_preserves_first.md`, `mdtests/count_to_three_bad_invariant.md`, `mdtests/count_to_three_bad_invariant_initialization.md` |
| Assertions and facts | Lean/Dafny/F* proof scripts | ghost assertion checking | `at statement N { assert ... by auto; }`, later `have`, `exact` | `mdtests/count_to_three_at_loop_invariants.md`, `mdtests/count_to_three_bad_assert.md` |
| Proposition syntax | Lean/Isabelle/Dafny/F* specifications | kernel `And`, `Or`, `Not`, `Implies`, `ForAll` propositions | `and`, `or`, `not`, `implies`, `forall` | `mdtests/click_proposition_logic.md`, `mdtests/forall_array_segment.md`, `mdtests/forall_array_segment_rejects_overwritten_cell.md` |
| Rewriting and simplification | Lean `simp`, Isabelle simplifier | rewrite theorem application | later `simp`, `rewrite`, `calc` | not yet on the C path |
| Bitvector arithmetic | SMT, CBMC, hardware-oriented provers | bitvector32 solver/normalizer | later `bitvector` | partially through `auto` |
| Frame reasoning | separation logic, C verifiers | pre/post memory evaluation with symbolic initial cells and loop write footprints | `auto`, later `frame` | `mdtests/write_second_old_preserves_first.md`, `mdtests/write_second_old_rejects_overwritten_cell.md`, `mdtests/fill_tail_preserves_first.md` |
| C array surface syntax | C frontends, C verifiers | parameter-array lowering to pointer parameters | ordinary C/Click signatures | `mdtests/fill3_array_loop.md`, `mdtests/copy3_array_demo.md` |

## Current C0 Boundary

The current C0 subset is enough to make the first several categories
executable: scalar code, signed-overflow undefined behavior, pointer range
checks, bounded loops, known function calls, memory postconditions,
first-frame postconditions with `old(...)`, C-style array-parameter syntax, and
Click proposition syntax with `and`, `or`, `not`, `implies`, and `forall`.
`auto` can prove simple quantified array-segment postconditions, including
unchanged-memory cases and frame facts outside a loop write footprint.
Structural-label ghost checks for `assert` and `invariant` currently use the
executable fragment of proposition syntax. Invariant failures are reported as
loop-entry or preservation obligations. Annotated scalar and pointer-safety
loops can now be summarized without unrolling: Click checks invariant
initialization, one-step preservation, exit facts from the invariant plus the
false loop condition, and a first write-footprint frame fact for loads provably
outside the symbolic loop writes.

It is not yet enough for the full launch-shaped proof story. The main missing
pieces are quantified memory-segment invariants, full memory-changing loop
invariants, richer intermediate fact management, richer C integer operations and
casts, local arrays, richer memory predicates, and general frame conditions.

That is intentional. The mdtests should make the next missing piece obvious:
when a proof pattern needs a new C0 feature, add the feature because the proof
capability demands it, not because C has it.
