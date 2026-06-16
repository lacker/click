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
- A **tactic** is a proof-language command that tries to prove a theorem or
  reduce the proof to simpler goals.
- A **proof** is a `by` clause: either one tactic call, or a block containing a
  sequence of tactic calls.

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
| Pointer range safety | C verifiers, separation logic | memory-validity and range axioms | `auto`, later `bounds` or `frame` | `mdtests/pointer_range.md` |
| Memory postconditions | ACSL/Dafny/F* function contracts | final-state memory evaluation | `auto`, later `frame` | `mdtests/fill3_memory_postconditions.md`, `mdtests/fill3_bad_memory_postcondition.md` |
| Bounded loops | bounded model checking, symbolic execution | budgeted loop execution | `auto`, later `bounded_check` | `mdtests/bounded_loop.md`, `mdtests/fill3.md` |
| Function calls | modular verification, inlining, call summaries | function environment and specification satisfaction | `auto`, later `use specification` | `mdtests/function_call.md` |
| Loop invariants | Dafny/F*/Why3/Frama-C | ghost loop-head checks now, later while-invariant checker | `at loop N { invariant ... by auto; }`, later verification-condition generation | `mdtests/count_to_three_at_loop_invariants.md`, `mdtests/count_to_three_bad_invariant.md` |
| Assertions and facts | Lean/Dafny/F* proof scripts | ghost assertion checking | `at statement N { assert ... by auto; }`, later `have`, `exact` | `mdtests/count_to_three_at_loop_invariants.md`, `mdtests/count_to_three_bad_assert.md` |
| Rewriting and simplification | Lean `simp`, Isabelle simplifier | rewrite theorem application | later `simp`, `rewrite`, `calc` | not yet on the C path |
| Bitvector arithmetic | SMT, CBMC, hardware-oriented provers | bitvector32 solver/normalizer | later `bitvector` | partially through `auto` |
| Frame reasoning | separation logic, C verifiers | pre/post memory evaluation with symbolic initial cells | `auto`, later `frame` | `mdtests/write_second_old_preserves_first.md`, `mdtests/write_second_old_rejects_overwritten_cell.md` |

## Current C0 Boundary

The current C0 subset is enough to make the first several categories
executable: scalar code, signed-overflow undefined behavior, pointer range
checks, bounded loops, known function calls, memory postconditions,
first-frame postconditions with `old(...)`, and structural-label ghost checks
for `assert` and `invariant`.

It is not yet enough for the full launch-shaped proof story. The main missing
pieces are non-unrolling loop induction and verification-condition generation,
richer intermediate fact management, richer C integer operations and casts,
local arrays, richer memory predicates, and general frame conditions.

That is intentional. The mdtests should make the next missing piece obvious:
when a proof pattern needs a new C0 feature, add the feature because the proof
capability demands it, not because C has it.
