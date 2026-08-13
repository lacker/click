# Simple verification lacks a deterministic scaling gate

Click has deterministic per-tactic work budgets and wall-clock integration
profiles, but neither detects a path whose cost grows quadratically while the
current fixtures remain small. The efficiency contract requires simple
verification to be output-sensitive `N log N` or better. We need a gate that
measures growth, not only an absolute ceiling.

## Required design

Add an in-process Rust scaling harness over generated, valid C and Click. It
must call the shared verification engine directly and collect deterministic
work without subprocesses, stderr parsing, or wall-clock assertions. Each
axis should run at four geometrically increasing sizes after a small warm-up:

- unrelated functions and verified rules;
- straight-line statement/program-point count;
- ambient exact facts and condition facts;
- surface proposition spellings;
- resource facts and definition members;
- global theorem declarations; and
- claims sharing one function execution.

Record total work and the responsible named operation spans. The assertion
should allow fixed startup and logarithmic indexing factors while rejecting a
clear quadratic curve. Keep generated fixtures small enough for the ordinary
test suite once the intended bound is met.

## Regression design

Start with at least `N = 32, 64, 128, 256` for each isolated axis. Where the
current implementation is already too slow, a smaller four-point sequence is
acceptable only if it still distinguishes linear from quadratic growth. The
failure should identify the axis, measurements, and adjacent growth ratios.

The initial harness may land with known failing curves asserted as focused
ignored tests, each linked to its issue below. The harness and at least one
green control curve must run by default; do not quarantine the entire suite.

## Acceptance criteria

- Measurements use deterministic verifier work, not elapsed time.
- Fixtures exercise explicit simple tactics only.
- A deliberately quadratic reference workload makes the ratio check fail.
- A linear green control passes on all supported test configurations.
- Every performance issue in the burndown names the scaling axis that closes
  it.

## Implemented axes

The default in-process gate now covers unrelated functions/rules, unrelated
global theorems, explicit theorem dependencies, straight-line statements with
retained program-point snapshots, exact `assumption()` with geometrically
increasing unrelated ambient facts/surface spellings, composite-resource
definition members, and claims sharing one checked function execution. Kernel
resource regressions separately cover exact lookup, unrelated normalization,
and adjacent interval merging.

The remaining harness work is richer named-operation work attribution: the
curves currently report total deterministic work and their scaling axis, but
do not yet break a failed curve down by operation span. Dedicated `step()
using`, transport, and same-kernel/many-surface-spellings curves remain tracked
by `indexed-proof-fact-and-surface-spelling-stores.md`.

The composite-member curve exposed a separate representation hazard before it
could measure useful work: expanded function requirements form a deep theorem,
and each verified claim cloned that immutable proposition recursively. Theorem
values now share their proposition through `Arc`, making claim-level theorem
clones constant-time and stack-safe without changing the logical shape that
certificate replay consumes. Independently, the general conjunction builder
is balanced; a 1,024-leaf structural regression fixes its expected depth at
10. The default composite-member curve now reaches 64 members using only
explicit `step() using {}` and `frame() using {}` tactics.
