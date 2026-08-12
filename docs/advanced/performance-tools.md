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

This page assumes the target has already been classified using
[Triaging Proof Failures](proof-failure-triage.md). Performance tools diagnose
tooling slowness or optimize a correct proof; they do not decide whether a
failed claim is false, missing proof steps, or blocked on Click functionality.

Correctness comes first. Run `click verify` before starting optimization work:

```text
click verify
    correctness failure -> repair the proof
    timeout/slowness    -> profile diagnostically
    success             -> profile for optimization -> expand -> verify
```

A prompt proof failure is not a performance profile target. Fix it with
ordinary proof steps before interpreting timing hotspots or expanding earlier
tactics. Profiling a target that cannot complete is appropriate only when the
timeout or unexpected slowness is itself the problem: that report is a partial
diagnostic frontier, not an optimization profile, and it offers no expansion
commands.

They also do not promise that smart tactics find every proof. Click requires
sound, replayable smart successes and prompt, bounded smart failures; search
completeness is a non-goal. When search fails normally, split the work into
smaller smart tactics or provide an explicit simple proof. Change shared search
heuristics only for a general measured pattern, not to force one example
through a single broad tactic.

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
shape. Proof-level `if`, frontier-local `branch`, and `loop` are CONTROL. A `have` is structurally a
control node, but its source site is SMART when its supported body is smart,
SIMPLE when its nonempty body is entirely simple, and otherwise CONTROL. That
inherited source-site class is shared by timing, smart-site inventory, and
expansion, so a profile can legitimately list `have` under SMART or SIMPLE.

A successful smart tactic must construct a `SimpleProof`, a structured proof
whose `SimpleProofStep` leaves are surface-expressible simple tactics. A simple
proof may retain the control structure needed to replay branches and scopes,
so expansion is not necessarily a flat or nonempty list of steps. Click prints
that typed proof as ordinary `.click` syntax and independently replays it
before accepting the smart success.

An unsuccessful smart tactic has no simple proof to expand. Errors created
inside tactics retain the originating timing identity, so the profiler can
distinguish a failed smart attempt from a successful expansion candidate.
An ordinary bounded failure is a proof-authoring result, not an engine bug.
It becomes a tooling problem if it misses its deadline, emits an unusable
diagnostic, behaves unstably, or reveals that the proof cannot be continued
with supported simple tactics.
Smart execution uses finite execution/search budgets, `click profile` has an
outer project deadline, and `click expand` has a 60-second default whole-command
deadline that can be overridden explicitly. That one deadline covers source
discovery, certificate generation, replay verification, and the final output
gate; the phases do not each receive a fresh allowance. An expired expansion
reports the interrupted tactic or verifier phase and writes no artifact.

## The simple-proof boundary

The implementation keeps source proofs and expanded proofs distinct:

- `ProofTactic` is the parsed source representation and may contain smart,
  simple, or control operations.
- `SimpleProof` is the result of a successful smart tactic. It recursively owns
  `SimpleProofStep` values, so it cannot contain a smart tactic or an internal
  replay operation.
- Search evidence (kernel derivations and certified transitions) is consumed
  transiently while constructing that result. It is not printed, profiled as
  an independent source tactic, or accepted as evidence that expansion
  succeeded; there is no retained internal plan between search and the
  `SimpleProof` it constructs.

`SimpleProofBuilder` stores typed simple steps while internal search evidence is
lowered. Once construction succeeds, Click structurally prints the same
`SimpleProof` as ordinary `.click` syntax and independently replays it. There
is no second tactic-selection phase between construction and printing.

This boundary gives expansion failures four distinct meanings:

1. Search did not find an internal proof route. This can be ordinary bounded
   smart-search incompleteness.
2. Search found a route, but Click could not construct a `SimpleProof`; the
   diagnostic identifies missing simple-proof evidence or surface support.
3. A `SimpleProof` was constructed, but its independent replay failed; the
   planner emitted an incomplete or incorrect simple proof.
4. Replay succeeded but the rewrite failed to parse, verify, or reach an audit
   fixed point; this is expansion-tool integration failure.

Do not collapse these categories into a generic certificate failure. In
particular, category 3 is not repaired by adding replay fallback search: the
smart planner must put every fact and rule it used into the `SimpleProof`.

## What is enforced today

Ordinary verification stops a tactic when it exhausts its deterministic work
budget (cooperative prover checkpoints; SIMPLE 500,000, SMART and CONTROL
2,000,000), so pass/fail does not depend on machine speed or load. A
real-time backstop behind it catches stretches of work the checkpoints do
not count, measured as **exclusive per-thread CPU time** on Unix: scheduler
contention is not charged, and a container does not inherit its children's
cost. Platforms without a thread CPU clock fall back to exclusive wall-clock
time. The backstop defaults are SIMPLE 5 s, SMART 2 s, and CONTROL 6 s;
profile reporting still flags SIMPLE at 500 ms and CONTROL at 2 s so slow
operations remain visible findings without becoming machine-dependent
verdicts. Kernel expression, statement, call, loop, and path checkpoints
observe the active deadline, and the failure names the class, claim,
statement, source tactic, the spent work or elapsed time, and the limit.
`CLICK_DISABLE_TACTIC_BUDGETS=1`
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
  smart tactic above the configured threshold in a fully verified target. A
  correctness failure instead produces explicitly incomplete diagnostic
  output and no expansion command; a timeout produces a partial timeout
  diagnosis. Its default project limit is 30 seconds, and `--top` controls the
  number of function and claim attribution rows (default 8).
- `click expand [--output PATH | --in-place] <sidecar.click|mdtest.md>:<line>:<column>`
  requires the selected proof unit to verify, replaces one successful smart
  tactic, then verifies the complete rewritten proof unit and the transitive
  contracts it calls before writing it. A failure later in the selected proof
  blocks expansion of an earlier tactic by design; restore proof correctness
  before doing performance work. An unrelated broken proof unit does not block
  expansion, and unselected source text is preserved byte-for-byte. Its default
  limit is 60 seconds; `--time-limit` overrides it.
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

- `SimpleProof` is the smart/simple boundary; a smart success is accepted only
  after its deterministic steps have been printed and independently replayed.
- Smart tactics are best-effort conveniences, not proof-language primitives:
  failure within a stated bound is allowed, while the required proof must
  remain expressible as smaller or simple steps.
- Never hide a slow simple tactic by expanding an enclosing smart tactic.
- `ProofSite` and one-based `PATH:LINE:COLUMN` locations are shared by
  verification, profiling, expansion, auditing, and rewriting.
- `click expand` directly verifies every rewrite before output; `click audit`
  additionally checks retained-session equivalence, cold verification, and
  the expansion fixed point.
- Expansion is an optimization of a green proof, not a repair mechanism:
  selected-proof correctness precedes profiling and expansion, and the
  rewritten selected proof must remain correct.
- Kernel Click has no textual syntax. Tool output is documented Surface Click
  accepted by the ordinary parser. Canonical struct spellings include
  `owner->field`, `owner->pointer_field[start..end]`, and `object(owner)`.
- Everything consumed by certificate replay needs a checked surface spelling.
- Snapshot-qualified spelling search indexes the memories nested anywhere in
  the kernel proposition, tries exact recorded states before marker-compatible
  states, and constructs candidates only from those states. It never truncates
  a candidate list by count or combines a fact with unrelated program points.
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
  30 seconds per sidecar, matching `click verify`) — example-project harness
  controls.
- `CLICK_DISABLE_TACTIC_BUDGETS`, `CLICK_DISABLE_DECIDE_MEMO`,
  `CLICK_DISABLE_CERT_ARMS`, `CLICK_DISABLE_MEMORY_DAG`, and
  `CLICK_DISABLE_CLOSER_REUSE` — A/B handles; each restores its pre-feature
  path.

The `UNATTRIBUTED` row remains intentional: a new unknown timing event or
accounting inconsistency is incomplete evidence instead of being silently
forced into the nearest named bucket.
