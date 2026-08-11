# Owned-segmented-buffer order weakening has no named simple certificate

`examples/owned-segmented-buffer` fails ordinary verification:

```text
`owned_segmented_buffer_init.contract` path 0, tactic 1: `have` failed:
post-execution simplification proved `0 <= owner->first_len`, but Click has no
explicit simple certificate for that derivation
  selected premises: at(statement(4).entry, 1) <= at(statement(4).entry, first_len)
```

Smart simplification proves `0 <= x` from an available `1 <= x`, but the
expansion vocabulary has no named simple rule for signed order weakening
(transitivity through a constant bound), so certificate lowering fails after
the search succeeds. The failure surfaced when commit `e9460ff` ("Reject
opaque outcome certificates") removed the fallback that previously hid it.

Per the migration convention, the fix is the smallest named simple rule —
a standard-theorem application in the `int32_increment_*` family style, e.g.
an `int32_order_weakening`/transitivity theorem whose exact proposition is
checked against kernel axioms — not a generic arithmetic solver relabeled as
simple.

## Reproduction

```sh
target/debug/click verify examples/owned-segmented-buffer
```

The project is quarantined in `tests/examples.rs` until this is fixed.

## Acceptance criteria

- The unchanged owned-segmented-buffer project verifies and leaves quarantine.
- A focused syntax/mdtest regression expands a `0 <= x` goal from a `1 <= x`
  (or `c <= x`) premise through the new named theorem followed by
  `assumption`.
- The fix does not restore opaque certificates and does not widen any
  existing simple rule into a search.
