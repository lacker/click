# Replay predicate transport across local stores

## Problem

At a frontier reached after initializing stack locals, a predicate over
unchanged external memory is definitionally the same fact as at function
entry. Smart `transport` proves that relationship, but certificate lowering
fails to make its premises replayable:

```text
could not make fact transport premises explicit:
explicit surface premises do not replay the certified fact transport
```

The concrete reproduction carries `sorted(p, 3)` across declaration and
assignment of a local loop index before using it as a loop invariant. The C
does not write through `p`. This is a certificate bug, not a reason to move
the loop proof back to function entry or alter the C.

## Minimal regression

Require an opaque predicate over `int32 p[3]`, execute only local declaration
and assignment statements, then transport the entry predicate to the current
frontier and use it to initialize a frontier-local loop invariant.

## Acceptance criteria

- Smart transport emits a simple certificate that freshly replays across
  local-only memory changes.
- The certificate relies only on checked statement effects and does not make
  internal memory summaries assumable.
- The migrated `loop_sorted_range_invariant` proof verifies unchanged.
- `click expand` and `click audit` accept the transport and nested invariant
  proof sites.
