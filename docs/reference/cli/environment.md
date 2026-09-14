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

### `CLICK_VIEW_SEMANTICS`

Stable views are the default interpretation of `views`. Set
`CLICK_VIEW_SEMANTICS=legacy` to select the retiring weak-view
interpretation for an A/B comparison; unset or `stable-loans` is the
ordinary gate. Any other value is rejected, so a misspelled selection cannot
quietly run under the wrong semantics.

`click verify`, `click profile`, `click expand`, and `click audit` read the
variable once at startup and run everything they check under the selected
interpretation, including the verification of a rewrite an expansion
produces. The mdtest and example harnesses read it too, selecting the mode
per fixture. The mode is part of every proof-artifact identity, so a result
from one mode never certifies a claim in the other; `--changed-since`
baseline markers already record every `CLICK_*` variable that was set, so a
baseline attested under one mode is not reused under the other. The
body-rerun ratchet is skipped under `legacy`.

This is rollout scaffolding for the stable-view cutover in
`issues/fix-views.md`. It is removed, with the legacy interpretation, when
that interpretation is deleted.
