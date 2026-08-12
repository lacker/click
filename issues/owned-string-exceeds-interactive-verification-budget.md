# Owned-string verification exceeds the interactive budget

The fully verified `examples/owned-string` project takes about 35 seconds
warm on the development machine with `--time-limit 120s`, past its default
30-second project limit. Every certificate gap is fixed (the pure
pointer-offset identity, the branching disjunction lowering, and the
`le`-then-`lt` transitive `have` sites all construct and replay explicit
simple certificates), so this deadline is now the only reason the project
remains quarantined in `tests/examples.rs`. Under the default limit the
truncation currently reports as a ghost-region mismatch
(`issues/deadline-truncation-masquerades-as-ghost-region-mismatch.md`).

An earlier `click profile examples/owned-string` run at about 27 seconds
reported:

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

The certificate fixes completed the previously failing proofs (the
`owned_string_clear` and `owned_string_pipeline` sites now verify instead of
erroring out early), which accounts for the growth from 27 to 35 seconds:
more claims complete, none regressed. The performance problem itself is
unchanged and does not come from any one tactic crossing its budget.

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
- The project passes repeatedly under its default 30-second limit, quiet and
  under moderate load, and leaves the `tests/examples.rs` quarantine.
- Deterministic work limits guard the reduced certification, control, and core
  regressions so correctness does not depend on machine speed.
- `click profile` names the responsible nested operation whenever a control
  container crosses its budget.
- No speedup comes from weakening claims, changing the C, raising budgets,
  caching an uncertified result, or retaining ambient `derive` reconstruction.

