# Performance tools: profile, expand, audit

Three tools work together so Click users can speed up code, diagnose
slowness, and detect performance bugs in Click itself.

## The model

1. The tests work and are fast.
2. Every tactic is classed smart or simple (the verifier decides).
3. Simple tactics are fast — always.
4. `click-profile` reports any slow tactic, in projects and mdtests
   alike.
5. A slow SIMPLE tactic is an error in Click, and the profiler says so.
6. A slow SMART tactic is expanded by `click-expand` into simple ones.
7. Profile-then-expand accounts for ALL slowness. Corollaries:
   - Expansion REDUCES slowness to simple-tactic slowness; a
     certificate whose replay is slow is an engine bug per rule 5, not
     a resting state.
   - Smart search must be bounded: a failing tactic should fail fast,
     and slow failure is a profiler finding. (Enforcement of this
     corollary is not yet implemented.)
   - Non-tactic machinery (certification, environment building) is
     held to the simple standard; the profiler's UNATTRIBUTED bucket
     must stay ~0.
8. `click-audit` checks expansion works across whole projects; its
   purpose is detecting bugs in Click itself.

## Budgets are enforced in the regular test passes

The mdtest and examples harnesses fail a passing test whose tactic
broke its class budget, measured as EXCLUSIVE time (a container does
not inherit its children's cost): SIMPLE 500 ms, SMART/CONTROL 2 s.
Violations found under the parallel suite re-run serially and only
repeat offenders fail (wall-clock noise under load is not a finding).
`CLICK_DISABLE_TACTIC_BUDGETS=1` bypasses, for archaeology only. A
test that exceeds `MDTEST_TIME_LIMIT` (default 30 s) fails naming the
tactic it was inside.

## Tool notes

- `click-profile <project|mdtest.md|dir>` — per-tactic exclusive
  SIMPLE/SMART/CONTROL/certification split plus an unattributed
  remainder; prints the `click-expand` command for each slow smart
  site. Quarantine does not apply.
- `click-expand <sidecar.click|mdtest.md>:<line>:<col>` — emits the
  rewritten source on stdout (whole markdown for mdtests, coordinates
  as click-profile prints them). Expansion emits the exact accepted
  certificate — no second proof search. An empty expansion deletes the
  tactic: a smart tactic whose certificate contributed no surface
  tactics was redundant.
- `click-audit` — walks a project's smart sites: expand, verify, check
  the site count drops. Defaults: stop at first failure, 10 s
  slow-site limit, 10 m run limit, resume via the printed `--start-at`.

## Settled invariants

- TacticCertificate is the smart/simple boundary; a smart success must
  replay through a surface-expressible certificate before acceptance.
- Simple tactics are deterministic replay; never hide a slow simple
  tactic by expanding an enclosing smart tactic.
- ProofSite + one-based PATH:LINE:COLUMN are shared by verification,
  profiling, expansion, auditing, and rewriting.
- click-expand does not reverify; verification and auditing stay
  separate composable operations.
- Kernel Click has no textual syntax; all output is documented Surface
  Click accepted by the ordinary parser. Canonical struct spellings:
  `owner->field`, `(owner->pointer_field)[start..end]`, `object(owner)`.
- Everything the certifier consumes gets a surface spelling.
- An empty proof `if` branch is legal: it contributes its case split
  and every path goal stays owed at path end.

## Tooling flags

- `CLICK_TIMINGS=1` — per-tactic and certification-phase timing lines.
- `MDTEST_FILTER=<name>`, `CLICK_RUN_QUARANTINED=1`,
  `MDTEST_TIME_LIMIT=<duration>` — mdtest harness controls.
- `CLICK_DISABLE_TACTIC_BUDGETS`, `CLICK_DISABLE_DECIDE_MEMO`,
  `CLICK_DISABLE_CERT_ARMS`, `CLICK_DISABLE_MEMORY_DAG`,
  `CLICK_DISABLE_CLOSER_REUSE` — A/B handles; each restores the
  pre-feature path exactly.
