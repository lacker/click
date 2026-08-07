# Preserve ghost-resource identity in execution expansion after `branch`

## Problem

After a frontier-local `branch`, an `execute()` in the common continuation can
verify normally but fail when expanded. The selected execution certificate is
reconstructed separately inside the generated proof-level path cases. A
semantically unchanged ghost resource can then receive a different internal
identity, so replay rejects the expanded proof even though its displayed
resource expressions are identical.

The owned-vector `vector_replace_if` proof exposes this when its detached
`reach` is replaced by a frontier-local `branch`. Direct expansion of the
common `execute()` reports that the execution proof changed more than its
certified ghost-resource representation:

```text
return value: desired v1000003, certified v1000005
memory snapshots differ
missing certified resources: [views owner[...]]
extra certified resources: [views owner[...]]
```

The missing and extra resource spellings are the same. This is an
expansion/replay disagreement, not smart-search incompleteness and not a reason
to retain `reach` as a permanent proof-shaping workaround.

During a full audit, expansion of the same `execute()` also spent its complete
two-second tactic budget inside a generated `frame` before failing locally.
That diagnostic is properly bounded, but the expansion path should not depend
on repeating smart resource reconstruction when it already has a successful
execution certificate.

## Minimal regression

Reduce the existing `vector_replace_if` case from
`src/lang/click/expansion.rs` while preserving these ingredients:

- an owned composite resource containing a pointer-backed slice;
- two opaque calls, one in each C branch, which return the selected value;
- a frontier-local `branch` proof of the C `if`;
- a common `execute()` followed by resource framing and a postcondition proof.

The ordinary proof must verify first. Expanding the common `execute()` must
then produce a simple certificate which reverifies from function entry. Keep
the original C unchanged.

This regression is distinct from deferred post-execution expansion: selecting
the final common `simp()` in the same frontier-local proof already expands and
replays with the deferred branch-context aggregation support.

## Design direction

- Give execution-certificate replay a stable correspondence for return values,
  memory snapshots, and ghost resources across generated proof path cases.
- Compare or remap ghost resources by their certified semantic origin rather
  than incidental fresh IDs created during reconstruction.
- Reuse the successful execution certificate instead of asking a generated
  smart `frame` to rediscover its resource alignment.
- Preserve exact-resource checks: do not weaken replay to ignore real resource
  additions, losses, or changed snapshots.

## Acceptance criteria

- The reduced frontier-local `branch` regression verifies normally.
- Expanding its common `execute()` reverifies without an internal identity
  mismatch.
- The selected site passes `click audit` within the normal tactic budget.
- A negative regression still rejects a certificate that truly changes a
  ghost resource or memory snapshot.
- The owned-vector `vector_replace_if` proof can migrate from detached `reach`
  to frontier-local `branch`, and every smart site in that claim passes audit.
- No C reshaping, arbitrary limit increase, replay relaxation, or retained
  smart tactic in the supposedly expanded certificate is used as a workaround.

## Blocks

This blocks the remaining `reach` migration in `vector_replace_if`. It does
not block the simpler branch-continuation fixtures or deferred final-tactic
expansion.
