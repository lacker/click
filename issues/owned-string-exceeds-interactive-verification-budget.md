# Owned-string verification exceeds the interactive budget

The fully verified `examples/owned-string` project takes about 35 seconds
warm on the development machine with `--time-limit 120s`, past its default
30-second project limit. Every certificate gap is fixed (the pure
pointer-offset identity, the branching disjunction lowering, and the
`le`-then-`lt` transitive `have` sites all construct and replay explicit
simple certificates), so this deadline is now the only reason the project
remains quarantined in `tests/examples.rs`. Under the default limit the
truncation reports the active outer deadline.

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

## 2026-08-12 narrow attribution update

The profiler now reports nested operation aggregates instead of leaving the
dominant work in broad control/core buckets. On a representative complete
30.054s run, the major overlapping totals were:

```text
contract symbolic execution             16.669s / 10 calls
contract derived entry facts             13.432s / 10 calls
derived forall proposition checks         13.365s / 417 calls
resource representation checks             3.916s / 24 calls
whole-contract certificate replay          2.301s / 8 calls
```

The contract body executor itself accounted for only 3.116s. Thus the main
certification cost was not C execution; it was repeatedly proving the same
closed, verified quantified theorem facts while constructing each function's
contract entry context. A success-only kernel cache now retains a closed
`forall` only after proving it from no function-specific assumptions (or from
previously retained closed facts). On loaded follow-ups, expensive `forall`
checks fell from 280 to 50--60 and contract symbolic execution fell from the
16--22s range to 12--19s. The result is material but still well above the
under-five-second acceptance target, so the issue and quarantine remain.

The next isolated targets are the remaining context-dependent quantified
facts and the owned-string pipeline resource containment check (roughly
2.3--5.2s depending on host load). Whole-contract replay is about 2--5s in
aggregate and is a secondary, measured contributor rather than the dominant
one.

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
