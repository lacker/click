# Preserve old-snapshot loadability after free

## Problem

An entry-state value postcondition such as

```click
ensures forall (k: int32) {
    0 <= k and k < old(owner->len) implies
        owner->data[k] == old(owner->data[k])
};
```

cannot currently be lowered after the function frees the old allocation. Click
reports the entry-memory element load as non-loadable even though the unfolded
entry resource supplied a loadable range covering it.

This confuses two different claims. A load from the freed allocation in the
post-state is invalid; a load from the immutable function-entry snapshot is a
historical value and remains valid evidence. Malloc-copy-free replacement
needs the latter to state content preservation without retaining access to the
retired allocation.

## Intended regression

Use a focused function that owns an allocated `int32` range, saves or copies
one entry value, frees the allocation, and returns with a postcondition about
`old(data[index])`. Include symbolic index bounds so the regression exercises
range-derived loadability rather than only a materialized constant cell.

The current-memory spelling `data[index]` after free must still fail. The
entry-snapshot spelling `old(data[index])` must lower and verify from the
entry loadable range.

## Acceptance criteria

- Allocation retirement affects the post-state lifetime only; it does not
  invalidate loads already justified in an older memory snapshot.
- Symbolic old-element loads derive from an old loadable range plus their
  bounds after free.
- A focused positive/negative regression distinguishes historical loads from
  use-after-free.
- Owned-vector growth can state copied-prefix preservation directly with
  `old(owner->data[k])`, without ghost storage or artificial C changes.
- Kernel, mdtest, and example suites remain green.
