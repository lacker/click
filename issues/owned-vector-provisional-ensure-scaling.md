# Owned-vector provisional ensure lowering repeatedly scans range facts

## Violated invariant

After the scoped resource repair and dynamic returned-allocation transition
succeed, verifying `allocated_vector_push.contract` must remain within the
ordinary verifier budget. A simple verified-call transition may inspect its
explicit inputs and affected state, but must not repeatedly rescan a growing
path-wide fact context for each dynamic range comparison.

## Reproduction

In `examples/owned-vector/vector.click`, replace the persistent
`observe(allocated_vector(owner))` in the full-capacity branch with an
`open(allocated_vector(owner)) { ... }` scope containing the three preparatory
steps, so the scope closes before `vector_grow(owner)`.

With the returned-allocation/caller-frame fix in place, use the existing
explicit statement operation for the `vector_grow` call while the ordinary
statement-step replay handoff is incomplete:

```click
step() using {
    owner->cap <= 536870910;
}
```

This is a diagnostic route through the already checked multi-successor
operation, not the intended final surface proof. A plain `step()` must work
again when `replay-smell.md` retires the parallel exactly-one adapter.

Then run:

```text
click profile examples/owned-vector --time-limit 30s
```

The resource transition advances, but the profile times out in the
`c(grown) == 0` proof branch. On the current 2026-08-23 development baseline it
reports:

- 22.821 seconds in `vector_push` provisional ensure lowering;
- 98,586 `range membership: offset equality` calls taking 8.998 seconds; and
- 26.714 seconds of interrupted verifier-core work at the 30-second deadline.

The focused dynamic reallocation mdtest remains fast, so this is not necessary
cost for classifying allocation continuity. The uncommitted owned-vector proof
edit is only the end-to-end trigger; reduce the repeated range query into a
small deterministic scaling regression before changing the engine. Keep this
issue separate from the resource roadmap because the violated invariant is
general ensure-lowering complexity and the likely repair is a fact-query index
or memo boundary, not resource lifetime semantics.

## Intended regression

Construct several otherwise-equivalent verified-call states whose unrelated
exact path facts grow geometrically while the call's dynamic mutable ranges and
ensures remain fixed. Count range-membership/equality work for provisional
ensure lowering. The curve must be linear up to indexing factors in the facts
that can actually support the queried ranges, rather than repeating scans of
the complete context for every comparison.

## Acceptance criteria

- A deterministic multi-size regression reproduces the repeated dynamic-range
  equality work without using wall-clock timing as its verdict.
- Provisional ensure lowering indexes or caches the relevant exact range facts
  and does not rescan unrelated path facts per comparison.
- The scoped `allocated_vector_push.contract` verifies under the ordinary
  30-second project limit with no raised budgets or weakened proof/C source.
- `click profile examples/owned-vector` reports no simple-engine bottleneck.
- The owned-vector proof repair can land, the example leaves quarantine, and
  this issue is deleted.
