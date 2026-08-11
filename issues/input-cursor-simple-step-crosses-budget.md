# Input-cursor simple step crosses its class budget under audit

`click audit examples/input-cursor` fails during session initialization:

```text
tactic budget exhausted: tactic `step` in `input_cursor_shared_pipeline.contract`
exceeded its 500ms simple real-time limit after 0.501s (statement 5, source
tactic 11); a slow simple tactic is a Click engine bug
```

Ordinary `click verify` passes, so this is not a correctness regression and
the project is not quarantined. But a simple tactic crossing its class budget
is on the always-track list, and a 1ms overrun of a wall-clock limit is
machine-speed dependent: the same project can pass or fail audit run to run.

Two intertwined problems:

- the `step` at statement 5 performs too much work for a simple statement
  transition — profile where the time goes and reduce it, or the certificate
  is not proportional to its work;
- the budget is enforced in wall-clock time, so enforcement is
  nondeterministic near the limit. The perf issues already call for
  deterministic work accounting; simple-tactic budgets should move to it.

## Reproduction

```sh
target/debug/click audit examples/input-cursor
```

## Acceptance criteria

- `click audit examples/input-cursor` completes its session and audits all
  42 sites.
- The `step` cost is attributed and reduced, or shown to be proportional to
  its certificate with the budget expressed in deterministic work units.
- No budget is raised merely to make the audit pass.
