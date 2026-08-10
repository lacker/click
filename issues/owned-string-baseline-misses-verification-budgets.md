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

After the example harness was aligned with ordinary `click verify`, the same
unchanged project exposed a stronger deterministic failure in
`owned_string_push`: execution replay returned the final `owner->len` load,
while fresh kernel certification returned the value stored there,
`old(owner->len) + 1`, and path pairing did not recognize the two certified
spellings as equal. The focused selected proof unit is:

```text
click verify --time-limit 10s \
  examples/owned-string/owned_string.click:247:5
```

This is replay/certification disagreement, not an acceptable proof failure.
Path equivalence must use the equations proved by each path's certified store
records rather than comparing final return terms without their execution
provenance.

The store-return disagreement now has a focused passing regression, but the
whole project is still not stable enough to rejoin the green example gate. A
standalone run has passed while a subsequent serial-suite run rejected
`owned_string_pipeline` at the replay/certification boundary: the replay had
folded `empty_owned_string(owner)`, while fresh certification retained
`owned_string(owner)` plus projected views. The two names expose the same
owned body under the proved `owner->len == 0` fact. Representation comparison
must accept that checked fold/unfold change without accepting unrelated added
ghost ownership. Until this passes repeatedly, `owned-string` is listed in
the example harness quarantine and remains runnable with
`CLICK_EXAMPLE=owned-string`.

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
- The selected `owned_string_push` proof pairs replay and certification when
  their return values are equivalent through certified store equations.
- Folded resource renaming is accepted only when definitional consumption
  accounts for all owned resources; unrelated ghost ownership remains
  rejected by the kernel.
- No budget is raised and no C source or proof obligation is weakened.
- The verifier reports one stable, local budget failure if the regression is
  deliberately made expensive.
