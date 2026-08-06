# Keep modular-call snapshot provenance stable

## Problem

The source-faithful owned-vector pipeline can complete smart search for the
general `vector_push` call, but its generated certificate initially fails
replay. The relevant postconditions combine two snapshots—for example, the
exit `owner->len` equals the entry `owner->len + 1`—and certificate
reconstruction does not retain a stable Surface Click spelling for every such
public fact.

A prototype recorded statement entry/exit states and synthesized all four
operand placements for public comparison facts. It made the focused two-call
counter regression pass, but it was not globally sound as a source-level
change. The clean example gate exposed four regressions:

- binary-tree and ring-buffer expansions emitted statement-local frame
  witnesses with proof closers that did not replay;
- input-cursor crossed its smart-tactic budget under the changed certificate
  context; and
- owned-string's existing `at(statement(0).entry, ...)` premises no longer
  selected the same exact facts.

Changing a frame witness from `normalize` to `assumption` globally only traded
one set of failures for another. The closer must be validated against a fresh
lowering of the emitted surface proposition, and adding statement provenance
must not silently reinterpret existing source anchors.

## Violated invariant

A smart tactic's success is useful only if its emitted certificate replays in
a fresh verification session. Program-point provenance must be stable and
local: recording a public fact at one statement cannot change which kernel
fact an existing spelling selects elsewhere in the proof.

## Intended regressions

Add a focused three-file fixture with a `struct counter`:

1. `zero(counter)` ensures `counter->value == 0`;
2. `increment(counter)` ensures both its result and the exit field equal the
   entry field plus one; and
3. `pipeline(counter)` calls both modularly and proves `result == 1` and
   `counter->value == 1`.

The pipeline must verify, expand, and replay without manually restating the
callee's mixed-snapshot postcondition.

Keep the existing owned-string, input-cursor, binary-tree, and ring-buffer
examples as compatibility regressions. They exercise source anchors, local
frame transports, and repeated modular calls that the narrow counter fixture
does not.

## Design direction

Give every certified public call postcondition an explicit provenance record
containing its source statement and exact entry/exit snapshot identities.
Surface reconstruction should query that record rather than inserting global
candidate spellings into an undifferentiated map.

When an emitted certificate needs a statement-local frame witness, lower the
actual emitted proposition in a fresh source context and select `normalize`,
`assumption`, `derive`, or explicit `transport` only when that exact closer
replays. Do not infer the closer from the kernel target alone: a kernel fact
that normalizes can lower from an `at(entry)/at(exit)` spelling to two distinct
memories on fresh replay.

Statement numbering must come from one shared source-layout traversal used by
execution, structural proofs, expansion, and replay. If an older path used a
loop index or a synthetic assertion index as a statement index, migrate it
deliberately with regressions rather than changing the mapping incidentally.

## Acceptance criteria

- The two-call counter regression verifies and its smart proof expands to a
  replayable certificate.
- The general-vector pipeline no longer reports search success followed by
  certificate replay failure.
- A public mixed-snapshot postcondition has a stable, unambiguous Surface Click
  spelling tied to the source call.
- Frame-witness closers are checked against fresh surface lowering.
- Existing `at(statement(...))` proofs retain their meaning, or any deliberate
  migration is explicit and mechanical.
- owned-string, input-cursor, binary-tree, ring-buffer, the full example gate,
  profile, expansion, and audit all pass within their normal budgets.
