# Environment variables

Click's ordinary user workflow does not require environment variables. The
variables on this page enable diagnostics, fixture selection, or controlled
contributor experiments.

## Diagnostic variables

| Variable | Effect |
| --- | --- |
| `CLICK_TIMINGS=1` | Emit per-tactic and verification-phase timing lines. Prefer `click profile` for a reconciled report. |
| `CLICK_TIMING_STARTS=1` | Emit internal timing-start events for engine diagnostics. |
| `CLICK_FULL_DIAGNOSTICS=1` | Disable bounded diagnostic rendering and expose full internal state. Use only for reduction and engine investigation. |

Normal diagnostics deliberately bound internal terms. Do not recommend
`CLICK_FULL_DIAGNOSTICS` as a workaround for an enormous default diagnostic;
fix the bounded diagnostic instead.

## Fixture selection

| Variable | Effect |
| --- | --- |
| `MDTEST_FILTER=TEXT` | Run mdtests whose filename contains `TEXT`. |
| `CLICK_EXAMPLE=NAME` | Run the named example project. |
| `CLICK_RUN_QUARANTINED=1` | Include quarantined mdtests or examples. An explicit filter also selects its matching quarantined fixture. |

## Contributor A/B controls

| Variable | Effect |
| --- | --- |
| `CLICK_DISABLE_TACTIC_BUDGETS=1` | Disable per-tactic budget enforcement for reduction and archaeology. Outer command limits still matter. |
| `CLICK_DISABLE_DECIDE_MEMO=1` | Disable assumption-decision and equality-graph memoization. |
| `CLICK_DISABLE_CERT_ARMS=1` | Restore the pre-feature contract-certification arm path. |
| `CLICK_DISABLE_MEMORY_DAG=1` | Disable memory-derivation DAG storage and use the fallback path. |
| `CLICK_DISABLE_CLOSER_REUSE=1` | Disable reuse of planner-verified closers. |

These variables are internal experiment handles, not stable user features.
Use them only for an A/B regression that names the expected invariant. Remove a
handle when the corresponding fallback is no longer intentionally maintained.
