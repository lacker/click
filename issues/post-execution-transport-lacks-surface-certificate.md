# Post-execution transport cannot emit its surface certificate

The remaining `derive using` block for `terminated_at` in
`examples/owned-string/owned_string.click` hides two ordinary fact transports.
After `owned_string_push` stores the new length and terminator, the proof needs
to carry these exact facts to the current frontier:

```click
at(statement(3).exit, owner->len)
    == at(statement(3).entry, index + 1)

at(statement(4).exit, owner->data[index + 1]) == 0
```

The target facts re-express the same values using `old(owner->len)` and the
current memory snapshot. Splitting the old broad derivation into two bare
`transport(source, target)` tactics is the intended smart-to-simple workflow,
but verification fails during certificate construction with:

```text
post-execution fact transport has no explicit surface-premise certificate
```

This is not ordinary smart-search incompleteness: search has selected a
transport, but Click cannot turn that selection into a replayable
`transport(...) using { ... }` proof. Ambient `simp()` is not an alternative;
on this reduced goal it reaches the smart tactic's two-second limit, and the
three facts listed by the legacy `derive using` do not prove the current-state
goal by themselves.

## Regression

Extract the unchanged `owned_string_push` C function and the smallest resource
contract that preserves these two statement snapshots. The proof should:

1. execute through the terminator store and return;
2. transport the length-store equality to
   `owner->len == old(owner->len) + 1`;
3. transport the terminator-store equality to
   `owner->data[old(owner->len) + 1] == 0`; and
4. rewrite the index to prove `terminated_at(owner->data, owner->len)`.

Keep the original C stores, local `index`, and return shape. Do not introduce
proof-only C locals or reorder the implementation to make the snapshots easier
to relate.

## Acceptance criteria

- Each bare smart `transport` succeeds promptly from the verified execution
  history.
- `click expand` replaces each one with a small
  `transport(source, target) using { ... }` certificate.
- The expanded proof verifies from a fresh parse and contains no smart tactic
  or legacy `derive` at this site.
- Every emitted premise has an exact surface spelling and replays without
  ambient execution-history search.
- Missing surface evidence reports the specific unspellable kernel fact rather
  than the generic certificate error above.

