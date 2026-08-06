# Performance tools: profile, expand, audit

Three tools work together so Click users can diagnose proof cost, replace
successful automation with explicit replay, and test Click's expansion
boundary:

- `click profile` measures verification and identifies individual tactic
  hotspots;
- `click expand` replaces one successful smart tactic with its accepted
  surface certificate;
- `click audit` checks that expansion succeeds and reverifies across examples
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
It also inventories unique smart source sites separately from dynamic smart
attempts. One site can produce several attempts when multiple symbolic paths
or repeated claim execution revisit it.

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
- **CONTROL** tactics contain nested scripts and bookkeeping.

This is the class of the selectable source occurrence, not just its Rust AST
shape. Proof-level `if` and `reach` are CONTROL. A `have` is structurally a
control node, but its source site is SMART when its supported body is smart,
SIMPLE when its nonempty body is entirely simple, and otherwise CONTROL. That
inherited source-site class is shared by timing, smart-site inventory, and
expansion, so a profile can legitimately list `have` under SMART or SIMPLE.

A successful smart tactic must replay through a `TacticCertificate` whose
leaves are surface-expressible simple tactics. Certificates may retain the
control structure needed to replay branches and scopes, so expansion is not
necessarily a flat or nonempty list of simple tactics.

An unsuccessful smart tactic has no certificate to expand. Errors created
inside tactics retain the originating timing identity, so the profiler can
distinguish a failed smart attempt from a successful expansion candidate.
Smart execution uses finite execution/search budgets, `click profile` has an
outer project deadline, and `click expand` has a 60-second default engine
deadline that can be overridden explicitly.

## What is enforced today

Ordinary verification stops a tactic when its class deadline expires, measured
as **exclusive per-thread CPU time** on Unix: scheduler contention is not
charged, and a container does not inherit its children's cost. Platforms
without a thread CPU clock fall back to exclusive wall-clock time. The defaults
are SIMPLE 500 ms, SMART 2 s, and CONTROL 6 s. Profiling still flags CONTROL
bookkeeping at 2 s so it remains visible without making a non-expandable
container share the hard cutoff for smart search. Kernel expression,
statement, call, loop, and path checkpoints observe the active deadline, and
the failure names the class, claim, statement, source tactic, elapsed time, and
limit. `CLICK_DISABLE_TACTIC_BUDGETS=1`
bypasses enforcement for reduction and archaeology. `click profile` is itself
a diagnostic override: its project deadline remains hard, while individual
tactics are allowed to complete so the report can identify the slow operation.

These are per-operation tail guards. They are not an aggregate throughput
promise.

`click verify` also applies a 30-second outer limit independently to every
sidecar or selected proof unit. That outer deadline contains slow frontend,
environment, certification, verifier-core, or driver work that is not owned by
one tactic; it does not replace the class deadlines.

`click profile` reconciles direct verification wall time across frontend,
environment, exclusive SIMPLE/SMART/CONTROL time, kernel certification,
measured function work outside those operations (`VERIFIER CORE`), and
source-I/O/driver time (`PROCESS/DRIVER`). If the project deadline fires, the
engine records the active tactic or frontend, environment, certification,
verifier-core, or driver phase before scopes unwind. The unfinished residual
is reported separately as `INTERRUPTED`; a timed-out run is always diagnosed
as incomplete and never as healthy volume.
`UNATTRIBUTED` is reserved for an inconsistent or unknown remainder rather
than being a catch-all for known overhead. Work counts and conservative
development baselines then distinguish smart hotspots, simple engine bugs,
healthy volume, certification bottlenecks, setup bottlenecks, and incomplete
evidence.
Wall-clock baselines are deliberately conservative and are not a
machine-independent SLA.

For volume-bound runs, `TOP FUNCTIONS / CLAIMS BY EXCLUSIVE TIME` ranks the
semantic owners of the measured work. Function rows partition their time into
simple, smart, control, certification, and verifier-core buckets. Claim rows
use the same exclusive tactic measurements plus per-claim certification; a
`<shared verifier work>` row owns preparation, certification, and verifier-core
time that has no narrower claim identity. Claim rows therefore reconcile to
their function total, while the function and claim rankings are two views of
the same time and must not be added together. `click profile --top N` bounds
each ranking; it changes presentation only, never the performance diagnosis.

`click audit` checks every source-selectable smart site in passing example and
mdtest inputs, whether or not profiling called it slow. On the first site of a
claim it cold-verifies both the original and expanded proof units. A timing
regression must exceed both 2x and the configured 500 ms slack, then repeat in
a second serial comparison, before audit fails. Raw phase totals are still
printed but are not a size-independent performance verdict. A full audit is a
manual release/certificate-boundary gate, not part of ordinary `cargo test`.

## Using the tools

- `click profile <sidecar.click|project|mdtest.md|dir>` profiles examples and mdtests,
  ignores quarantine, and prints a `click expand` command for each completed
  smart tactic above the configured threshold. Its default project limit is
  30 seconds, and `--top` controls the number of function and claim attribution
  rows (default 8).
- `click expand [--output PATH | --in-place] <sidecar.click|mdtest.md>:<line>:<column>`
  parses and typechecks the sidecar, then verifies only the rewritten proof
  unit and the transitive contracts it calls before writing it. An unrelated
  broken proof does not block a targeted repair, and unselected source text is
  preserved byte-for-byte. Its default limit is 60 seconds; `--time-limit`
  overrides it.
- `click audit <sidecar.click|example|mdtest|directory|repository-root>` expands,
  retained-session verifies, compares original and expanded cold verification,
  and checks the claim's smart-site multiset strictly shrinks without
  introducing a new smart tactic. One path-aligned expansion may remove
  multiple symmetric occurrences. Passing progress is one row per claim by
  default; `--verbose` restores per-site timing rows. Repeat `--claim LABEL` to
  audit specific named proof units without locating their coordinates. Claim
  selection is exact and rejects unknown or cross-sidecar-ambiguous labels.
  Audit stops at the first failure by default and prints a resumable
  `--start-at` command that retains the selected claims and output mode. Point
  it at the repository root to cover both `examples/` and `mdtests/` in one
  run.

An empty expansion deletes the selected tactic: the successful smart tactic
contributed no surface certificate steps. Always verify and profile the exact
rewritten artifact before deciding that expansion improved performance.

## Settled correctness invariants

- `TacticCertificate` is the smart/simple boundary; a smart success is accepted
  only after deterministic certificate replay.
- Never hide a slow simple tactic by expanding an enclosing smart tactic.
- `ProofSite` and one-based `PATH:LINE:COLUMN` locations are shared by
  verification, profiling, expansion, auditing, and rewriting.
- `click expand` directly verifies every rewrite before output; `click audit`
  additionally checks retained-session equivalence, cold verification, and
  the expansion fixed point.
- Kernel Click has no textual syntax. Tool output is documented Surface Click
  accepted by the ordinary parser. Canonical struct spellings include
  `owner->field`, `owner->pointer_field[start..end]`, and `object(owner)`.
- Everything consumed by certificate replay needs a checked surface spelling.
- Reconstructing a surface spelling is itself bounded by shared structural
  depth and work limits. Exhaustion rejects the candidate and reports the
  reconstruction category without printing the potentially enormous kernel
  term; it never relaxes the subsequent parse, lowering, or replay checks.
- An empty proof `if` branch is legal: it contributes its case split, and every
  path goal remains owed at path end.

## Tooling flags

- `CLICK_TIMINGS=1` — per-tactic and certification-phase timing lines.
- `MDTEST_FILTER=<name>`, `CLICK_RUN_QUARANTINED=1`, and
  `MDTEST_TIME_LIMIT=<duration>` (default 30 s) — mdtest harness controls.
- `CLICK_EXAMPLE=<name>` and `CLICK_EXAMPLE_TIME_LIMIT=<duration>` (default
  10 minutes) — example-project harness controls.
- `CLICK_DISABLE_TACTIC_BUDGETS`, `CLICK_DISABLE_DECIDE_MEMO`,
  `CLICK_DISABLE_CERT_ARMS`, `CLICK_DISABLE_MEMORY_DAG`, and
  `CLICK_DISABLE_CLOSER_REUSE` — A/B handles; each restores its pre-feature
  path.

The `UNATTRIBUTED` row remains intentional: a new unknown timing event or
accounting inconsistency is incomplete evidence instead of being silently
forced into the nearest named bucket.
