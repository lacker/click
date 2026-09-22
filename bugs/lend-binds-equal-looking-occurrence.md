# The ordinary lend path binds a substitute occurrence, bypassing provenance

P1. Every escrowed view must anchor to the occurrence whose authority was
actually removed.

## What was found

The symbolic covering path of the stable-view planner re-resolves its
requirement against the post-reservation residual and refuses when the
resolved occurrence is not the checked one, with the explicit rationale
"an equal-looking occurrence would be lent instead of the one the coverage
was checked against" (`src/kernel/loans.rs:2196-2201`). The ordinary
(non-symbolic) cluster lend path at `loans.rs:2392-2400` resolves `selected`
and lends immediately with no equivalent `support != origin_support` guard —
although the same procedure maintains
`reserved_ownership_supports` with "the residual entry that actually
supplied the requirement" for exactly such provenance (2032-2075).

A normalization step between the reservation and the lend (split /
recombine) leaves a value-equal occurrence of the ownership support; the
ordinary path attaches the view binding to the substitute while the loan
issues for the substituted occurrence. Downstream, `recheck` and recovery
(`unique_owned_occurrence_for_fact`, `resource_algebra.rs:1794`) compare
support identities — never equal-looking values.

## Intended regression

Plan a stable view whose cluster's exclusive reservation consumes the
occurrence and one normalization step replaces it with a value-equal
entry; the plan must refuse (the symbolic guard's guard) until the
occurrence provenance is reconciled. Machine verification sketch: replay
a `plan_stable_view_transfer` over two `own(token T)` entries; after the
first entry's reservation, a planned cluster lends the surviving
value-equal occurrence with the recorded support id — the deciding
comparison is the plan's `support` id versus the borrowed occurrence id.

## Acceptance

- [ ] Every lend path re-derives (or refuses on) the `support !=
      origin_support` binding, mirroring the symbolic guard, with the
      substitute-occurrence regression refusing.
- [ ] `scripts/check.sh` green.
