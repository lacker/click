# Expand the slow input-cursor pipeline step

## Status

The unchanged `input-cursor` example verifies through the relevant smart
`step`, but that tactic deterministically exceeds the two-second smart-tactic
budget. The default example gate reported 2.014 seconds at statement 5, source
tactic 11 in `input_cursor_shared_pipeline.contract` on both the recovery
worktree and an isolated worktree at `9cd5bbb`. This is therefore a pre-existing
baseline failure, not a regression from the fixed-array frontier-loop work.

The example is explicitly quarantined until the slow successful tactic is
expanded or decomposed. Run it directly with:

```sh
CLICK_EXAMPLE=input-cursor cargo test --test examples -- --nocapture
```

## Classification

This is not evidence that smart search must become complete or that its shared
heuristics should be retuned. The tactic succeeds; under Click's performance
model, it is an expansion candidate. The open question is whether `click
expand` produces a fast, replayable sequence of simple tactics for this site.
If expansion fails, disagrees with profiling, or emits a certificate that does
not replay, that tooling failure takes priority and should be reduced here.

Do not raise the tactic budget, change the C pipeline, weaken the contracts, or
specialize shared search heuristics to make this fixture green.

## Acceptance criteria

- Profile the unchanged sidecar and identify statement 5, source tactic 11 as
  the same slow smart site reported by the fixture.
- Expand that successful site into replayable simple tactics, or replace it
  with an independently understandable explicit proof if expansion shows that
  the source tactic is too broad.
- The unchanged C and its contracts verify within all tactic-class budgets.
- `click audit examples/input-cursor` passes.
- Remove `input-cursor` from `tests/examples.rs` quarantine and restore the
  complete default test suite.
