# Performance tools: profile, expand, audit

Three tools work together so Click users can diagnose proof cost, replace
successful automation with explicit replay, and test Click's expansion
boundary:

- `click-profile` measures verification and identifies individual tactic
  hotspots;
- `click-expand` replaces one successful smart tactic with its accepted
  surface certificate;
- `click-audit` checks that expansion succeeds and reverifies across examples
  and mdtests.

The tools explain expensive verification; they do not promise that every
expensive project can be made small by expanding tactics. Healthy proof volume
is a valid diagnosis.

## Performance model

Verification time grows with proof work. A large project can legitimately take
longer because it performs many individually healthy operations. The target is
therefore predictable cost per stable unit of explicit proof work, not constant
time for every project and not one universal time per source statement.

A useful model is:

```text
total time ~= fixed setup
           + smart-search work
           + non-execution simple replay work
           + C execution work
           + control-flow bookkeeping
           + certification work
           + unexplained work
```

Source statements are only a rough orientation measure: statements differ in
complexity, and expansion intentionally replaces one statement with several.
More stable units include completed simple certificate leaves, C transitions,
claims, certification paths, and smart attempts. The profiler reports those
counts, total/average/maximum tactic costs, and setup and certification rates.

This model distinguishes two kinds of slowness:

- **hotspot-bound** work contains one unusually expensive operation;
- **volume-bound** work contains many operations running at a healthy rate.

Expanding a smart hotspot can trade search for longer but predictable replay.
It cannot eliminate healthy volume. A slow simple tactic remains an engine
problem, because expansion cannot make deterministic replay simpler.

## Tactic classes

The verifier, rather than the profiler, classifies tactics:

- **SIMPLE** tactics perform deterministic replay operations;
- **SMART** tactics perform contextual reasoning, search, or orchestration;
- **CONTROL** tactics such as `have`, proof-level `if`, and `advance` contain
  nested scripts and bookkeeping.

A successful smart tactic must replay through a `TacticCertificate` whose
leaves are surface-expressible simple tactics. Certificates may retain the
control structure needed to replay branches and scopes, so expansion is not
necessarily a flat or nonempty list of simple tactics.

An unsuccessful smart tactic has no certificate to expand. Errors created
inside tactics retain the originating timing identity, so the profiler can
distinguish a failed smart attempt from a successful expansion candidate.
Smart execution uses finite execution/search budgets, `click-profile` has an
outer project deadline, and `click-expand` has a 60-second default child
deadline that can be overridden explicitly.

## What is enforced today

The mdtest and example harnesses fail a passing test whose tactic exceeds its
class budget, measured as **exclusive** time: a container does not inherit its
children's cost. The defaults are SIMPLE 500 ms and SMART/CONTROL 2 s.
Violations found under the parallel suite rerun serially, and only repeat
offenders fail. `CLICK_DISABLE_TACTIC_BUDGETS=1` bypasses this check for
archaeology. An mdtest that exceeds `MDTEST_TIME_LIMIT` (default 30 s) fails
and names the active tactic when one is known.

These are per-operation tail guards. They are not an aggregate throughput
promise.

`click-profile` reconciles child-process wall time across frontend,
environment, exclusive SIMPLE/SMART/CONTROL time, kernel certification, and an
`UNATTRIBUTED` residual. A residual over 250 ms or 10% is an explicit
`UNEXPLAINED` diagnosis. Work counts and conservative development baselines
then distinguish smart hotspots, simple engine bugs, healthy volume,
certification bottlenecks, setup bottlenecks, and incomplete attribution.
Wall-clock baselines are deliberately conservative and are not a
machine-independent SLA.

`click-audit` checks every source-selectable smart site in passing example and
mdtest inputs, whether or not profiling called it slow. On the first site of a
claim it cold-verifies both the original and expanded proof units. A timing
regression must exceed both 2x and the configured 500 ms slack, then repeat in
a second serial comparison, before audit fails. Raw phase totals are still
printed but are not a size-independent performance verdict. A full audit is a
manual release/certificate-boundary gate, not part of ordinary `cargo test`.

## Using the tools

- `click-profile <sidecar.click|project|mdtest.md|dir>` profiles examples and mdtests,
  ignores quarantine, and prints a `click-expand` command for each completed
  smart tactic above the configured threshold. Its default project limit is
  30 seconds.
- `click-expand <sidecar.click|mdtest.md>:<line>:<column>` writes rewritten
  source to stdout. It does not modify or reverify the source. Its default
  limit is 60 seconds; `--time-limit` overrides it.
- `click-audit <example|mdtest|directory|repository-root>` expands,
  retained-session verifies, compares original and expanded cold verification,
  and checks the claim's smart-site multiset strictly shrinks without
  introducing a new smart tactic. One path-aligned expansion may remove
  multiple symmetric occurrences. Audit stops at the first failure by default and prints a
  resumable `--start-at` command. Point it at the repository root to cover both
  `examples/` and `mdtests/` in one run.

An empty expansion deletes the selected tactic: the successful smart tactic
contributed no surface certificate steps. Always verify and profile the exact
rewritten artifact before deciding that expansion improved performance.

## Settled correctness invariants

- `TacticCertificate` is the smart/simple boundary; a smart success is accepted
  only after deterministic certificate replay.
- Never hide a slow simple tactic by expanding an enclosing smart tactic.
- `ProofSite` and one-based `PATH:LINE:COLUMN` locations are shared by
  verification, profiling, expansion, auditing, and rewriting.
- `click-expand` does not reverify; verification and auditing remain separate
  composable operations.
- Kernel Click has no textual syntax. Tool output is documented Surface Click
  accepted by the ordinary parser. Canonical struct spellings include
  `owner->field`, `(owner->pointer_field)[start..end]`, and `object(owner)`.
- Everything consumed by certificate replay needs a checked surface spelling.
- An empty proof `if` branch is legal: it contributes its case split, and every
  path goal remains owed at path end.

## Tooling flags

- `CLICK_TIMINGS=1` — per-tactic and certification-phase timing lines.
- `MDTEST_FILTER=<name>`, `CLICK_RUN_QUARANTINED=1`, and
  `MDTEST_TIME_LIMIT=<duration>` — mdtest harness controls.
- `CLICK_DISABLE_TACTIC_BUDGETS`, `CLICK_DISABLE_DECIDE_MEMO`,
  `CLICK_DISABLE_CERT_ARMS`, `CLICK_DISABLE_MEMORY_DAG`, and
  `CLICK_DISABLE_CLOSER_REUSE` — A/B handles; each restores its pre-feature
  path.

The `UNATTRIBUTED` row remains intentional: new uninstrumented work is reported
as incomplete evidence instead of being silently forced into the nearest
tactic or setup bucket.
