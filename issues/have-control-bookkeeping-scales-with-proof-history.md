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

## Current diagnosis

A stage-by-stage trace of the three slowest blocks found distinct symptoms of
the same missing replay provenance:

- the `terminated_at` derivation spends about 1.3s in target/premise
  derivation over a large snapshot term;
- the unchanged `owner->cap` derivation spends about 3.8s in
  `equal_by_premise_chain`; and
- the unchanged `owner->data` derivation spends about 3.2s in
  `pointer_offset_equality_by_frame`.

Caching the ambient `Assumptions` construction removed repeated construction
but did not materially change those times. Narrowing the frame facts helped
only slightly. Asking the execution memory DAG before the legacy frame prover
also did not answer these replayed snapshot spellings and merely added work
before fallback, so that change was discarded too.

The important gap is therefore not just an unindexed `Vec`. During explicit
certificate replay, the selected memory spellings no longer expose a usable
derivation path through the execution-recorded DAG. The checker falls back to
reconstructing the relationship from broad ambient equality, separation, and
effect facts. The principled fix is to preserve or reconnect certified memory
provenance when lowering the certificate, or to carry a compact indexed
effect graph as replay context. It is not to add another global prover
reordering, cache a failed heuristic answer, or special-case owned-string.

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
- The replayed source and target spellings either retain their certified
  memory-DAG identities or name an explicit compact effect path; replay does
  not rediscover that path from all ambient facts.
- A focused regression stays comfortably below the control budget with a
  large irrelevant prefix.
- `owned-string` verifies under the normal 30s project limit without proof or
  C reshaping.
- `click profile` attributes the remaining work to the actual nested tactics,
  with no multi-second unexplained CONTROL rows.
