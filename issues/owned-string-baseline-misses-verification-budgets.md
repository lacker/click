# Owned-string baseline misses verification budgets

The unchanged `examples/owned-string` project is not reliably verifiable by
the ordinary CLI within its existing budgets. On 2026-08-09, two consecutive

```text
target/debug/click verify examples/owned-string
```

runs failed in different places:

- the first reached the 30-second sidecar deadline while exact execution was
  certifying `owned_string_pop`; and
- the second exhausted the 6-second control-tactic budget in
  `owned_string_push.contract` at `have` proof 11, statement 6, source tactic
  11.

This was reproduced after restoring an attempted one-line `derive using` to
`simp() using` migration, so it is a baseline tooling failure rather than a
proof regression. Do not increase either limit, skip these functions, or
reshape their C or proof scripts merely to move work away from the slow path.

## Regression and diagnosis

Profile the named functions or reduce the slow `have`/exact-execution path to
the smallest proof fixture that crosses its tactic-class work or time budget.
The reduction must use the shared bounded verifier directly and must confirm
that interrupted verifier work exits. Determine why nominally identical
project runs report different first failures; diagnostics should identify the
same bounded unit consistently when no source changed.

## Acceptance criteria

- `click verify examples/owned-string` passes repeatedly within the current
  project and tactic limits on a normal development machine.
- A focused regression protects the slow verifier path independently of the
  large example.
- No budget is raised and no C source or proof obligation is weakened.
- The verifier reports one stable, local budget failure if the regression is
  deliberately made expensive.
