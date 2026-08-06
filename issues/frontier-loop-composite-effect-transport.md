# Preserve composite field identity through frontier-local loop calls

## Problem

Migrating `examples/perpetual-service` from a legacy `for loop(0)` clause to
the frontier-local `loop` tactic exposes a real semantic gap.  The loop owns a
folded composite resource whose body includes both an object and a backing
cell:

```click
resource service(owner: struct service*) {
    owns owner->phase;
    owns owner->cell;
    owns owner->cell[0..1];
    fact separate(memory(object(owner)), memory(owner->cell[0..1]));
}
```

One arbitrary iteration calls an already verified C function that mutates
`owner->phase` and `owner->cell[0]` but does not mutate the `owner->cell`
pointer field.  The loop declares the same mutable footprint.  The legacy loop
proof verifies promptly.

The frontier-local preservation proof currently loses the certified identity
of `owner->cell` across the opaque call.  At the back edge, effect replay sees
the call's writes and the current field-derived segment, but cannot prove that
the segment has the same base as it had at loop entry.  A bare smart `step()`
spends its budget looking for a certificate; replacing it with the honest
simple `step() using {}` exposes the missing cross-snapshot fact immediately.

This is not permission to change the C, weaken the loop effect, unfold the
resource permanently, or add a redundant invariant.  The callee contract
already certifies that the pointer field is outside its mutable footprint.

## Required model

Frontier-local preservation must retain or reconstruct the certified frame
consequence for fields not written by an opaque call.  In particular:

- the caller's folded composite resource remains available after the call;
- the callee effect establishes that `owner->cell` is unchanged;
- the resource's separation fact remains usable with the correctly aligned
  entry and back-edge field loads; and
- loop-effect replay can compare the declared field-derived segment against
  the call's certified writes without heuristic search.

Simply projecting owned composite cores at function entry is insufficient: it
makes the field loadable but does not transport its value across the call.
Re-observing the folded resource only at the back edge is also insufficient:
it proves a fact about the new field load, not equality with the loop-entry
load.  The fix must use the call's checked frame evidence.

## Minimal regression

Add a focused mdtest with:

1. a two-field owner containing a pointer to one backing cell;
2. a composite resource owning the fields and cell and recording object/cell
   separation;
3. an opaque verified callee that changes one scalar field and the backing
   cell, but not the pointer field;
4. a perpetual or one-iteration C loop calling that callee; and
5. a frontier-local loop effect over the scalar field and
   `owner->cell[0..1]`.

The preservation proof should have an explicit replayable simple path.  The
test must not depend on a bare smart `step()` finding the certificate.  Keep
the existing C source unchanged when migrating `perpetual-service` after the
focused regression passes.

## Tooling acceptance

- Verification completes within the ordinary tactic budgets.
- `click profile` attributes any planning only to explicit smart source sites.
- `click expand` produces a simple certificate for every smart tactic in the
  focused regression.
- `click audit` freshly verifies those expansions.
- No generated certificate relies on ambient facts that disappear on replay.

## Acceptance criteria

- The focused frontier-local regression verifies with the opaque callee and
  field-derived loop effect.
- The same proof still works if unrelated pure facts and resource views are
  added, so selection is not an accidental context-order dependency.
- `examples/perpetual-service` migrates without changing its C, weakening its
  resource, or raising a budget.
- The legacy loop path and the frontier-local path use the same checked
  call-frame consequence rather than separate ad hoc reasoning.
