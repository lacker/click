# Proof Landscape

This document tracks the proof capabilities Click should grow, how they relate
to familiar verification systems, and which markdown tests currently exercise
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
execution and spec-checking axioms in the megakernel.

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
  Relevant concepts include bounded execution, path splitting, overflow/UB
  checks, memory-safety checks, and counterexample-oriented diagnostics.

## Capability Matrix

| Capability | Common source | Click axiom family | Click tactic surface | Current mdtest |
| --- | --- | --- | --- | --- |
| Scalar execution | symbolic evaluators, SMT-backed automation | C expression/statement execution | `auto`, later `symbolic_execute` | `mdtests/scalar.md`, `mdtests/argument_result.md`, `mdtests/max_symbolic.md` |
| C undefined behavior | CBMC, Frama-C/WP, UBSan-style checks | UB-aware C execution | `auto`, later `check_ub` or VCG output | `mdtests/overflow.md`, `mdtests/increment_requires_no_overflow.md`, `mdtests/increment_without_requires.md` |
| Pointer range safety | C verifiers, separation logic | memory-validity and range axioms | `auto`, later `bounds` or `frame` | `mdtests/pointer_range.md` |
| Memory postconditions | ACSL/Dafny/F* function contracts | final-state memory evaluation | `auto`, later `frame` | `mdtests/fill3_memory_postconditions.md`, `mdtests/fill3_bad_memory_postcondition.md` |
| Bounded loops | bounded model checking, symbolic execution | budgeted loop execution | `auto`, later `bounded_check` | `mdtests/bounded_loop.md`, `mdtests/fill3.md` |
| Function calls | modular verification, inlining, call summaries | function environment and spec satisfaction | `auto`, later `use spec` | `mdtests/function_call.md` |
| Loop invariants | Dafny/F*/Why3/Frama-C | while-invariant checker | later `invariant` / `vcg` | not yet exposed in `.click` |
| Assertions and facts | Lean/Dafny/F* proof scripts | proposition introduction and checking | later `assert`, `have`, `exact` | not yet exposed in `.click` |
| Rewriting and simplification | Lean `simp`, Isabelle simplifier | rewrite theorem application | later `simp`, `rewrite`, `calc` | not yet on the C path |
| Bitvector arithmetic | SMT, CBMC, hardware-oriented provers | bv32 solver/normalizer | later `bv` | partially through `auto` |
| Frame reasoning | separation logic, C verifiers | pre/post memory evaluation with symbolic initial cells | `auto`, later `frame` | `mdtests/write_second_old_preserves_first.md`, `mdtests/write_second_old_rejects_overwritten_cell.md` |

## Current C0 Boundary

The current C0 subset is enough to make the first several categories
executable: scalar code, signed-overflow UB, pointer range checks, bounded
loops, known function calls, memory postconditions, and first-frame
postconditions with `old(...)`.

It is not yet enough for the full launch-shaped proof story. The main missing
pieces are `.click` syntax for invariants and intermediate facts, richer C
integer operations and casts, local arrays, richer memory predicates, and
general frame conditions.

That is intentional. The mdtests should make the next missing piece obvious:
when a proof pattern needs a new C0 feature, add the feature because the proof
capability demands it, not because C has it.
