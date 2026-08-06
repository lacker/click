# Replay frontier-loop store resource certificates

## Problem

During a frontier-local preservation proof, smart `step()` can successfully
plan an indexed store from an owned symbolic range, then emit a simple
`step() using { ... }` certificate that fails fresh replay:

```text
missing resource fact `owns p[i..i + 1]`
resource facts: [owns p[0..n]]
```

The planner used Click's checked resource splitting, but the generated
certificate records only pure premises and loses the resource transformation.
This is an expansion/replay bug. Do not weaken the loop, unroll the C, or add
proof-only C operations to manufacture the singleton ownership.

## Minimal regression

Use unchanged C for a symbolic fill loop over `p[0..n]`, with a quantified
written-prefix invariant. In the frontier-local `preserve` proof, the first
body statement stores through `p[i]`. Smart `step()` must expand to a simple
certificate that derives the singleton write authority from the owned range
and freshly replays.

## Acceptance criteria

- The migrated `fill_n_segment_invariant` proof verifies with the unchanged C
  and its symbolic owned range.
- The generated certificate explicitly and replayably accounts for the
  required resource split or uses a simple transition whose kernel contract
  performs that checked split.
- `click expand` and `click audit` accept the selected store step.
- No internal resource fact is exposed as an assumable surface proposition.
- Existing range-splitting and resource-preservation tests remain prompt.
