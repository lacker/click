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

- `int32` and byte-like `uint8`
- pointers, array parameters, and local fixed-size arrays
- array indexing, pointer arithmetic, pointer loads/stores, and local
  address-of
- local variables, assignment/update statement sugar, stores, conditionals,
  `while`, assignment-style `for` loops, and function calls
- signed arithmetic undefined behavior for overflow, division/remainder edge
  cases, and invalid shifts
- `uint8` promotion through arithmetic/comparison/shift/bitwise operations and
  checked `int32`-to-`uint8` narrowing
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
- pure Click `function` definitions with `let`, `if`, `.fold`, and calls
- named predicates
- explicit `unfold(predicate_name)`
- proof steps including `symbolic_execute()`, `bounded_execute()`,
  `loop_vc(loop N)`, `frame()`, `frame(loop N)`, `choose(...)`,
  `witness(...)`, `simp()`, and `close()`

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
- `uint8` byte buffers, checked narrowing, and byte-slice stdlib predicates.
- C-string predicate experiments: `cstr_prefix`, `cstr_len`, `cstr`, and
  `cstr_bounded`.
- Existential proof steps via `witness` and `choose`.
- Sorting demos:
  - `compare_swap2_sorted`
  - `compare_swap2_permutation`
  - `sort3_sorted`
  - `sort3_permutation`
  - `bubble_pass3_max_suffix`
  - `bubble_sort3_two_pass_sorted`
  - `sort3_permutation_predicate`
  - `bubble_sort3_loop_permutation`
  - `loop_stdlib_permutation_invariant`

## Recent Kernel/Prover Capabilities

Recent work added or exercised:

- a split `src/kernel/` implementation with `src/megakernel.rs` kept only as a
  compatibility facade
- `uint8` values, byte-width memory accesses, byte local arrays, and typed Click
  array refs
- signed multiplication, division/remainder, bitwise operations, shifts, and
  C0 update/for-loop sugar
- pure Click byte-slice and C-string predicates in `stdlib/prelude.click`
- old-state pure function lowering through loop invariants, including
  `old(count(...))`
- stdlib `permutation` proofs through loops using count-shaped fold support
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

The old permutation-through-loops blocker is no longer the main boundary.
`stdlib/prelude.click` now defines `count` and `permutation`, and the kernel has
general `RangeFold`/count-shaped proof support that lets stdlib permutation
proofs work for straight-line sorting examples, bounded loop-shaped examples,
and a direct loop invariant example.

The next design pressure should come from a small real-library pilot rather
than another toy proof. Click still lacks the C and memory features needed for a
json-c-shaped slice: structs, field access, heap allocation/free, broader
integer conversions, named constants/globals/string literals, and module-scale
spec organization. Choose a tiny frozen target first, then add the smallest
feature that lets that target verify.

## Near-Term Roadmap

1. Create a `third_party/` or `examples/real/` pilot area with one frozen
   json-c-shaped target function.

2. Add the smallest missing C0/frontend and memory features required by that
   pilot, likely structs/fields, a tiny heap API or specified `malloc`/`free`,
   or broader integer conversions.

3. Extend the C-string and byte-slice stdlib only where the pilot needs it.

4. Add more fold/range lemmas when an mdtest or pilot proof exposes a reusable
   pattern.

5. Make invariant proof blocks more expressive.
   - Current invariant proof blocks are still limited, mostly `by auto;` or
     unfold-only scripts.
   - Larger proofs likely want explicit entry/preservation subproofs.

6. Improve deterministic proof-step coverage.
   - Keep moving successful `auto` behavior into replayable proof steps.
   - Especially for loop VCs, frame/effect reasoning, and predicate unfolding.

7. Improve diagnostics for missing loop invariants, failed witnesses, and
   alias/frame facts.

## Important Files

- `README.md`: human-facing manifesto plus links into `docs/`.
- `docs/README.md`: current technical source-of-truth index.
- `src/kernel/`: C semantic objects, assumptions solver, theorem/proof
  procedures, and unit tests.
- `src/megakernel.rs`: compatibility facade that re-exports `src/kernel/`.
- `src/lang/click.rs`: Click sidecar parser/lowering/proof replay.
- `src/lang/c.rs`: C0 parser/lowering.
- `stdlib/prelude.click`: ordinary Click standard-library definitions.
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
