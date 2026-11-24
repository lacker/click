# Fold read ranges

An `Integer`-valued range-fold function over an `int32[]` or `uint8[]` argument is an
opaque application, and its array argument names a whole-block state. A
fact about `unmarked(visited, 0, i)` would therefore die at `visited[i] = 1`,
even though the fold reads only the cells below `i`. Click bridges such a
store with a kernel-checked read summary of the function's definition and an
explicit framing rule that consumes it. There is no new source syntax: the
summary is inferred from the existing definition, for example

```text
function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}
```

which, for fixed scalar arguments, depends only on `v[k]` for
`lo <= k < hi`. The implementation is `src/kernel/fold_read_summary.rs`; its
module comment states the soundness argument in full.

## Status

Checked summaries (step 1) and the explicit framing rule (step 2) have landed.
The written proof in `mdtests/sweep_maintains_a_zero_unmarked_count.md` now uses
pointwise separation and preservation followed by the existing `unmarked_frame`
lemma, as part of retiring legacy transport. Its omitted-proof companion,
`mdtests/sweep_prefix_survives_its_endpoint_store_by_solve.md`, retains coverage
of the fold read frame. Automatic reuse of an unchanged application (step 3)
is not started and not authorized; its requirements are below.

An "arrays agree on `[lo, hi)`" relation that pure functions could consume,
which would remove the `walk_frame` lemma the graph-search examples use to
move a `walk` between two states of a successor array, was considered and
deliberately not pursued.

## Two independent checks

The rule is extensionality. Fix the definition, pointer arguments, scalar
arguments, and other value arguments. If two array states agree on every
typed logical read in the inferred support, the two applications are equal:
the initial accumulators agree, and each iteration sees the same accumulator,
index, and cell (finite fold induction). An empty fold returns its initial
value.

1. **Definition checking** proves the support includes every read that can
   affect the result. `CheckedFoldReadSummary::check` walks the lowered body
   against an explicit whitelist once per verification.
2. **Framing** proves the selected effects preserve those reads between the
   two states. `frame_fold_application_transport` decides each recorded
   step between them from its own write set and the querying context's exact
   facts.

Neither substitutes for the other: an exact syntactic index match does not
establish byte disjointness, and a separation fact cannot justify an
incomplete summary. Logical reads stay total. The rule inserts no viewability
or initialization guard, produces no resource fact, and grants no C access; a
logical value equality never supplies read permission, initialization, or
allocation liveness (`mdtests/fold_read_transport_grants_no_c_read.md`).

## Supported definitions

The accepted shape is an `Integer`-valued, `int32`-indexed top-level range
fold:

- One `int32[]` or `uint8[]` parameter is read, and every read is exactly that parameter
  at the fold's own item binder (binder identity, not name); repeated
  reads, including in both arms of a conditional, are allowed.
- The endpoints are `int32` scalar parameters or literals, and the initial
  accumulator is memory-independent.
- The body uses the accumulator, index, scalar parameters, literals, total
  `Integer` arithmetic, comparisons, conditionals, and total conversions.

Anything else declines the whole definition: another index (`v[k + 1]`,
`v[v[k]]`), a nested fold, a recursive or opaque helper call, an address
escape, or a read in an endpoint or the initial accumulator. A declined
function verifies as before; only the framing improvement is unavailable.
An actual scalar argument that is itself a historical read keeps its own
dependency and load identity; changed endpoints or base pointers are never
equated by range framing.

The summary handle is kernel-owned, immutable, and scoped to the
verification: its fields are private, so the Surface registers a body
(`register_kernel_fold_read_definitions` in
`src/surface/lowering/annotations.rs`) but never states a summary. The same
definition governs unfolding and framing. Expanded source writes the original
application and ordinary proof steps, and a fresh verifier reconstructs the
summary from the definition.

## Framing and states

Pointer offsets are exact sums of sign-extended scaled `int32` terms, so the
interval occupies the contiguous bytes `[p + 4*start, p + 4*end)` with no
wraparound, and the rule needs no representable-span bound. A write misses
the interval when one exact order fact places it wholly below or above
(`end <= j` or `j < start`), or when a stated separation with exact
membership facts excludes it. Emptiness is used only when a fact or the
syntax proves `end <= start`; unknown order is not emptiness. No loop over
the numeric range is permitted.

The essential boundary is a store of one `int32` at the exact upper endpoint,
which lies outside the half-open interval. Wider or partially overlapping
writes, aliases without separation evidence, and writes inside the range are
refused. A call's checked write set is used through the same rule; an unknown
write set is not guessed disjoint. Allocation, free, lifetime end, loop havoc,
forgotten cells, and effects without a checked write set are crossed only
where the assumption-free whole-block rule already proves the block untouched.

The rule records nothing on the edge and caches nothing: each answer is a
checked derivation of one query, never an assumption-free name. Old facts stay
facts about their states; the framed application equality is the bridge.
Because the rule is a checked simple step that answers the same for every
caller, a smart tactic composing the checked transport reaches it too: `close()`
closes
`mdtests/sweep_prefix_survives_its_endpoint_store_by_solve.md`, and
`click expand` rewrites it into the explicit transport.

## Automatic reuse is not implemented

Step 3 would connect checked support to application construction and
statement effects, so an unchanged prefix value is reused without a written
`transport`. It must not make pure term comparison search for frame proofs,
and must not put context-dependent results into a global assumption-free term
cache. It needs reusable range versions, or equivalent persistent effect
summaries, alongside the current whole-block array naming, validated by the
repeated-store scaling test before it is accepted; an automatic path that
rescans the memory history per application is not acceptable. Do not add a
smaller span to a freely reusable array reference: support belongs to the
application and the checked definition that warrants it. A user-written
`reads` annotation, helper-summary composition, multiple arrays, offsets,
nested folds, and recursion each need separate evidence from real proofs.

## Regressions and scaling

- Kernel tests in `src/kernel/fold_read_summary/tests.rs`: every unsupported
  read pattern, byte-width boundary overlap, aliasing, lifetime and call
  edges, session poisoning, and deterministic scaling over body size,
  application count, unrelated facts, interval length, and store sequences.
- `fold_read_summaries_are_checked_from_the_lowered_declarations` in
  `src/surface/tests.rs` and
  `explicit_fold_read_transport_along_a_store_sequence_is_near_linear` in
  `src/scaling_tests/surface/tests/scaling_tests.rs`.
- The `mdtests/fold_read_transport_*.md` fixtures (positive and refused
  forms), `mdtests/sweep_maintains_a_zero_unmarked_count.md`,
  `mdtests/sweep_prefix_survives_its_endpoint_store_by_solve.md`, and the `mdtests/array_fact_does_not_survive_*.md` attacks,
  which state a fact reading a cell the step may write and are refused by
  both the whole-block version and the fold read frame.

Work follows [Verification efficiency](verification-efficiency.md): summary
checking is linear in the selected body, instantiation is proportional to its
small template, indexed lookup ignores unrelated facts, and work is
independent of the numeric interval length.

## Byte-array folds

The same checked summary accepts a single `uint8[]` parameter. Its body must
read a `uint8` cell at exactly the fold index with stride one; scalar widening
to `int32` keeps that read support. Instantiation checks the declared element
type, and framing uses one-byte intervals. A four-byte read or stride under a
byte-array declaration is refused. This supports the Rust byte-sum fixture
without changing state, separation, or access-authority rules.
