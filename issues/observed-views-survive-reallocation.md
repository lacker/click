# Observed views survive reallocation

## Violated invariant

When an owned heap allocation is retired, no resource derived from observing
that allocation may remain usable. The resource checker must either consume
or invalidate every child view at the lifetime transition, while retaining
views of unrelated live memory.

On current master (`b306ad0e`), `examples/owned-vector` fails promptly in the
`owner->len == owner->cap` branch of `allocated_vector_push.contract`:

```text
resource would remain usable after its allocation is freed:
views owner[(...old data base...)..(... + load(owner->cap))]
```

The proof owns `allocated_vector(owner)`, observes its owner fields and old
data range, then calls `vector_grow`, which may retire the old allocation.
The failure also reproduces before the final proof-object migration, so this
is not migration fallout. It supersedes the old owned-vector umbrella issue:
the silent path-drop guard already landed, while the old expansion-attribution
and giant-term diagnoses are not the current first failure and must be filed
again only if they reproduce after this lifetime bug is fixed.

## Intended regression

A small resource test observes a parent allocation into child views, retires
the allocation, and proves that all children referring to that allocation are
removed or rejected while an unrelated view remains available. The unchanged
owned-vector source is the end-to-end regression.

## Acceptance criteria

- The focused regression pins transitive invalidation at heap retirement.
- `allocated_vector_push.contract` advances past the current runtime error
  without editing its C implementation or weakening its contract.
- If a later independent tooling failure appears, it receives its own current
  reproduction and issue rather than being folded into this one.
- `examples/owned-vector` leaves quarantine and `scripts/check.sh` is green.
- This file and its Open-list line are deleted with the fix and regressions.
