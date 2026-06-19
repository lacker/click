# Agent State

This is not a literal serialization of model internals or hidden reasoning. It
is the actionable project state that should let a future agent resume work
without reconstructing the whole conversation.

Created: 2026-06-19

## Current Direction

Click is now pointed firmly at the megakernel roadmap. The old small/list-kernel
direction taught useful lessons, but it is not the main path. The medium-term
goal is to make Click good at verifying real C code, starting with the current
C0 slice and growing toward real C.

The core product shape is:

- C code in `.c` files.
- Click sidecar specifications/proofs in `.click` syntax, currently exercised
  primarily through markdown tests in `mdtests/`.
- An LCF-style theorem object internally, but with a large trusted megakernel:
  C-native semantic objects, proof-producing built-ins, and deterministic proof
  procedures are acceptable if they make C verification practical.

Current foundational names:

- `axiom`: built-in trusted theorem-producing thing, including what literature
  might call axiom schemas.
- `theorem`: a proved proposition.
- `tactic`: a thing a proof calls to prove theorems.
- `proof`: a sequence of tactic/proof-step calls.

The current stance on automation:

- `auto` may be heuristic and use whatever internal help is useful.
- Deterministic proof steps should be explicit, replayable, and should cite the
  facts/procedures they use where possible.
- A long-term goal is for successful heuristic proofs to become replayable
  deterministic certificates when the proof-step language can express them.

## Current Language/Model

C0 currently supports a useful C-like subset:

- `int32`
- pointers and array parameters/local arrays
- array indexing and pointer arithmetic
- local variables, assignment, stores, conditionals, loops, function calls
- signed overflow as undefined behavior
- memory safety obligations via `valid_range(...)`
- explicit aliasing/non-overlap facts via `disjoint(...)`

Click sidecar concepts currently include:

- `requires`
- `ensures`
- `old(...)`, meaning function-entry value/memory
- `assert`
- loop `invariant`
- effect clauses `mutable ...` and `immutable`
- loop `step { mutable ... }` for iteration-relative effects
- named predicates
- explicit `unfold(predicate_name)`
- proof steps including `symbolic_execute()`, `bounded_execute()`,
  `loop_vc(loop N)`, `frame(loop N)`, `simp()`, and `close()`

Important syntax/design points:

- `..` range syntax follows the Rust/Zig/D-style half-open convention.
- `mutable p[lo..hi]` means externally visible memory outside that range is not
  mutated. `immutable` means no externally visible memory is mutated.
- `preserves` and `writes_only` were intentionally replaced by
  `mutable`/`immutable`.
- `old(...)` inside a loop still means function entry, not previous iteration.
- Loop-level `mutable` clauses describe the whole loop; `step { mutable ... }`
  describes one iteration.

## Current Test/Demo State

The mdtest framework is the primary end-to-end proving harness. It parses
markdown files containing C code, Click sidecar specs, and expected pass/fail
results. Run it with:

```sh
cargo test mdtests -- --nocapture
```

The full suite was passing at the time this file was written:

```sh
cargo test
```

Current useful demos include:

- `fill3`, `fill3_array_loop`, and local array demos.
- Symbolic scalar loop invariants such as `count_to_n_loop_invariant`.
- Symbolic pointer loop safety with `valid_range(p[0..n])`.
- Quantified memory invariants, including old-memory invariants.
- Loop/function effect summaries with `mutable`, `immutable`, and `disjoint`.
- Copy-loop facts such as `copy_n_segment_invariant`.
- Sorting demos:
  - `compare_swap2_sorted`
  - `compare_swap2_permutation`
  - `sort3_sorted`
  - `sort3_permutation`
  - `bubble_pass3_max_suffix`
  - `bubble_sort3_two_pass_sorted`
  - `sort3_permutation_predicate`

## Recent Kernel/Prover Capabilities

Recent work added or exercised:

- finite `forall` instantiation for bounded integer ranges
- bounded finite context splitting for small symbolic integer ranges
- finite quantified order facts participating in transitive order reasoning
- scoped obligations under `implies`/`forall`, so memory-load obligations from
  guarded propositions do not escape unconditionally
- deeper variable collection/substitution through C-shaped propositions and
  terms
- bounded disjunction-case reasoning, narrowed so it does not explode on every
  proof goal

These were necessary to prove facts such as:

- one bubble-sort pass moves a maximum to the end:
  `mdtests/bubble_pass3_max_suffix.md`
- two-pass fixed-size bubble sort proves sortedness from loop VCs:
  `mdtests/bubble_sort3_two_pass_sorted.md`
- explicit six-way permutation can be packaged as a named predicate:
  `mdtests/sort3_permutation_predicate.md`

## Current Design Boundary

The next non-obvious design decision is permutation through loops.

What works:

- Straight-line three-cell permutation can be proved as an explicit six-way
  disjunction.
- The same six-way claim can be packaged as a `permutation3(...)` predicate and
  unfolded at the proof site.
- Fixed-size bubble-sort sortedness can be proved from loop VCs and quantified
  invariants.

What does not scale:

- Carrying `permutation3(...)` as a loop invariant through `bubble_sort3` causes
  a case-splitting blowup. Raw disjunction is the wrong shape for scalable loop
  permutation proofs.

Likely design options:

1. Add specialized swap/permutation facts.
   - Example: a compare-swap of adjacent cells preserves a permutation
     predicate.
   - Good for C sorting proofs quickly.
   - More ad hoc.

2. Introduce a finite multiset/count-style predicate.
   - Example: `count_in_range(p, lo, hi, x)` or a bag equality predicate.
   - Better general story for arrays and sorting.
   - Requires designing enough arithmetic/equality support for counts.

3. Keep fixed finite permutation predicates for now, but add proof procedures
   that reason about them without expanding to all disjunctive cases.
   - Pragmatic bridge.
   - Could become a dead end if not generalized.

My recommendation: do not push raw six-way disjunction further through loop
invariants. The next serious sorting step should introduce either a
swap-preserves-permutation axiom/tactic or a real bag/count-based permutation
predicate.

## Near-Term Roadmap

1. Decide how to represent permutation for loop proofs.
   - This is the current blocking design point.

2. After that decision, prove full three-cell bubble-sort correctness:
   - sortedness via existing loop VCs/invariants
   - permutation via the new representation

3. Make invariant proof blocks more expressive.
   - Current invariant proof blocks are still limited, mostly `by auto;` or
     unfold-only scripts.
   - Larger proofs likely want explicit entry/preservation subproofs.

4. Improve deterministic proof-step coverage.
   - Keep moving successful `auto` behavior into replayable proof steps.
   - Especially for loop VCs, frame/effect reasoning, and predicate unfolding.

5. Continue C0 growth only where proof pressure demands it.
   - Unsigned integers, casts, more widths, and real C parsing all matter, but
     the sorting/permutation proof model should be settled before broadening too
     much.

6. Split `src/megakernel.rs` once the current proof direction stabilizes.
   - It is large, but splitting before the proof model settles risks churn.

## Important Files

- `README.md`: project direction, current syntax, roadmap, and demos.
- `src/megakernel.rs`: C semantic objects, assumptions solver, theorem/proof
  procedures, and many unit tests.
- `src/lang/click.rs`: Click sidecar parser/lowering/proof replay.
- `src/lang/c.rs`: C0 parser/lowering.
- `tests/mdtests.rs`: markdown test harness.
- `mdtests/`: end-to-end examples and regression tests.

## Working Style Notes

- Prefer mdtests for user-visible proof scenarios.
- Prefer focused kernel unit tests for new solver behavior.
- Keep new proof procedures deterministic and capped if they can branch.
- If a proof gets slow, treat that as design signal, not just an optimization
  task.
- Avoid adding broad heuristics to deterministic tactics. `auto` can be
  heuristic; named proof steps should be predictable.

