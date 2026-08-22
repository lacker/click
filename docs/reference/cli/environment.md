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

### `CLICK_DISABLE_DECIDE_MEMO`

Set `CLICK_DISABLE_DECIDE_MEMO=1` to disable assumption-decision and
equality-graph memoization.

### `CLICK_DISABLE_CERT_ARMS`

Set `CLICK_DISABLE_CERT_ARMS=1` to restore the pre-feature
contract-certification arm path.

### `CLICK_DISABLE_MEMORY_DAG`

Set `CLICK_DISABLE_MEMORY_DAG=1` to disable memory derivation DAG storage and
use the fallback path.

### `CLICK_DISABLE_CLOSER_REUSE`

Set `CLICK_DISABLE_CLOSER_REUSE=1` to disable reuse of planner-verified
closers.

These variables are internal experiment handles, not stable user features.
Use them only for an A/B regression that names the expected invariant. Remove a
handle when the corresponding fallback is no longer intentionally maintained.
