# Environment variables

Click's ordinary user workflow does not require environment variables. The
variables on this page enable diagnostics, fixture selection, or controlled
contributor experiments.

## Diagnostic variables

### `CLICK_TIMINGS`

Set `CLICK_TIMINGS=1` to emit per-tactic and verification-phase timing lines.
Prefer `click profile` for a reconciled report.

### `CLICK_TIMING_STARTS`

Set `CLICK_TIMING_STARTS=1` to emit internal timing-start events for engine
diagnostics.

### `CLICK_FULL_DIAGNOSTICS`

Set `CLICK_FULL_DIAGNOSTICS=1` to disable bounded diagnostic rendering and
expose full internal state. Use this variable only for reduction and engine
investigation.

Normal diagnostics deliberately bound internal terms. Do not recommend
`CLICK_FULL_DIAGNOSTICS` as a workaround for an enormous default diagnostic;
fix the bounded diagnostic instead.

## Fixture selection

### `MDTEST_FILTER`

Set `MDTEST_FILTER=TEXT` to run mdtests whose filename contains `TEXT`.

### `CLICK_EXAMPLE`

Set `CLICK_EXAMPLE=NAME` to run the named example project.

### `CLICK_RUN_QUARANTINED`

Set `CLICK_RUN_QUARANTINED=1` to include quarantined mdtests or examples. An
explicit filter also selects its matching quarantined fixture.

## Contributor A/B controls

### `CLICK_DISABLE_TACTIC_BUDGETS`

Set `CLICK_DISABLE_TACTIC_BUDGETS=1` to disable per-tactic budget enforcement
for reduction and archaeology. Outer command limits still apply.

This variable is an internal experiment handle, not a stable user feature.
Use it only for an A/B regression that names the expected invariant. The
kernel reads no environment variable: its behaviour is fixed, and its
test-only audits are switched on by the tests that run them.
