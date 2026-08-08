# Nested `have` control bookkeeping scales with proof history

Profiling `examples/owned-string` under its normal 30s project limit shows
four small nested `have { derive using { ... } }` blocks in
`owned_string_push` taking about 2.6s to 4.9s each as CONTROL time. Their
actual smart work is much smaller; the project spends roughly 19.5s in
exclusive control bookkeeping and times out before completing later function
certification.

These are not difficult searches. Two of the slowest goals merely transport
an unchanged `owner->cap` or `owner->data` fact using one explicit premise.
Runtime should depend on the nested proof and its selected premises, not on
the complete earlier statement/snapshot history.

A focused timing audit localized the cost more precisely. Building the
post-execution `have` context, lowering the explicit premises, and recording
the certificate are all sub-millisecond. The multi-second cost is inside
`check_atomic_derivation_goal`: it repeatedly reconstructs assumptions from
the full ambient history and asks the general memory-DAG/frame equality
machinery to rediscover unchanged loads. A tempting reordering of the generic
memory prover did not improve this reliably and was discarded. The fix should
give explicit derivation replay an indexed or cached way to query the relevant
certified effect chain; it should not globally reorder memory reasoning based
on this one example.

Do not simplify the example proof merely to route around this cost and do not
raise the project or tactic limits. Identify which context cloning, surface
map reconstruction, deferred-certificate capture, or replay finalization is
charged exclusively to the `have` container and make it incremental.

## Minimal regression

Build a compact mdtest that creates many statement snapshots, then proves an
unchanged scalar or pointer-field equality with:

```click
have owner->field == old(owner->field) by {
    derive using { one_explicit_premise; }
}
```

Vary the number of irrelevant prior snapshots. Deterministic work and wall
time for the final `have` should remain approximately flat.

## Acceptance criteria

- The control container does not rescan or clone the complete ambient proof
  history once per nested tactic.
- Unchanged-load replay uses work proportional to the relevant effect chain
  and selected separation facts, not every prior equality and snapshot.
- A focused regression stays comfortably below the control budget with a
  large irrelevant prefix.
- `owned-string` verifies under the normal 30s project limit without proof or
  C reshaping.
- `click profile` attributes the remaining work to the actual nested tactics,
  with no multi-second unexplained CONTROL rows.
