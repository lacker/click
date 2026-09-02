# Split the two expansion census unit tests

Observed on 2026-09-01 while landing kernel fixes. `.config/nextest.toml`
says any unit test slower than 10 seconds is a bug to split or a prover
slowdown to fix, and kills a test at 60 seconds.

Two tests in `src/surface/tests/expansion_tests.rs` trip the slow threshold
on every green run and sit within a factor of two of the kill budget:

- `bound_universal_fixture_census_has_no_outcome_fallbacks`: 29.3 s and
  36.4 s on two idle-machine gate runs.
- `resource_example_pipelines_have_no_outcome_fallbacks`: flagged past 30 s
  on the same runs.

Each is a census: one test function verifies and expands a whole family of
fixtures or example pipelines. Under ordinary contention from other builds on
the same machine (load averages of 15 to 60 were observed), both cross 60
seconds and are killed, which turned four otherwise-green `scripts/check.sh`
runs red in one afternoon with no change to the code they exercise. Every
other test in the suite finished; the fixture harnesses run afterwards under
their own 20-minute containment and were never the problem.

## Violated invariant

A unit test's wall-clock budget is hang containment, not a proof budget: a
correct change must not fail the gate because the machine is busy. A census
test that already needs half the budget on an idle machine has no headroom.

## Intended regression

Split each census into one test per fixture family or example (or per
fixture, if the per-family time still exceeds 10 seconds), so that the
per-test time on an idle machine is well under the slow threshold and the
census's coverage is unchanged (the union of the split tests visits exactly
the fixtures the census visited; a test that enumerates the split list
against the fixture directory pins that).

## Acceptance criteria

- No unit test in `scripts/check.sh` exceeds 10 seconds on an idle machine;
  the two census tests are replaced by per-family tests with the same total
  coverage.
- A deterministic test pins that the split covers every fixture the original
  census enumerated.
- `scripts/check.sh` passes.
