# Owned-string verification exceeds the interactive budget

The fully verified `examples/owned-string` project currently takes about 27
seconds on the development machine, close to its 30-second project limit. A
representative `click profile examples/owned-string` run reported:

```text
26.797s total
  simple          821ms
  smart          5.609s
  control        6.790s
  certification  8.003s
  verifier core  5.510s
```

No completed simple tactic crossed 500ms and no smart tactic crossed two
seconds. The largest control container was the `terminated_at` `have` in
`owned_string_push` at 2.653s. Certification averaged 178ms per claim and
800ms per path. This means the project can be green while still being far too
slow for the normal edit/verify loop, and the current hotspot report does not
identify one nested operation that accounts for most of the delay.

This issue is separate from the post-execution transport certificate failure.
Fixing that proof site may remove some control work, but it does not by itself
explain eight seconds of certification and more than five seconds of verifier
core work.

## Regression

Preserve the full owned-string project as the integration workload, and add
machine-independent work accounting for its dominant certification, control,
and verifier-core paths. Reduce one representative claim for each dominant
phase so performance fixes can be tested without repeatedly running the whole
project.

The profiler should attribute expensive work inside a `have` to the actual
planning, surface-certificate construction, or replay operation instead of
leaving most of it as exclusive control-container time.

## Acceptance criteria

- Warm ordinary verification of the full project completes comfortably in the
  interactive range (target under five seconds on the development baseline),
  not merely just below the 30-second kill limit.
- Deterministic work limits guard the reduced certification, control, and core
  regressions so correctness does not depend on machine speed.
- `click profile` names the responsible nested operation whenever a control
  container crosses its budget.
- No speedup comes from weakening claims, changing the C, raising budgets,
  caching an uncertified result, or retaining ambient `derive` reconstruction.

