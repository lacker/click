# Fixture gates decide green from wall clock, so machine load flips the verdict

## Violated invariant

`scripts/check.sh` is the single source of truth for "is this tree green",
and its exit status is the verdict. A verdict that depends on how busy the
machine is cannot serve that role: the same commit passes on an idle
machine and fails on a loaded one, and neither run is more authoritative
than the other.

The fixture gates enforce real-time limits. `tests/mdtests.rs` gives each
mdtest `DEFAULT_MDTEST_TIME_LIMIT` (30s, overridable through
`MDTEST_TIME_LIMIT`), and `tests/examples.rs` gives each example project
the same treatment through `CLICK_EXAMPLE_TIME_LIMIT`. Both are wall
clock.

Observed on 2026-08-19 while landing the load-canonicalization work: a
full `scripts/check.sh` run failed with
`mdtests/bubble_sort3_loop_permutation.md` over its limit at a load
average around 25, and the same tree passed the same gate at a load
average around 9. Nothing about the tree changed between the runs. The
comment in `scripts/check.sh` already anticipates part of this — it runs
the fixture gates with `--test-threads 1` so the harnesses do not compete
with each other — but that only removes self-inflicted contention, not
load from anything else on the machine.

This matters beyond flakes. Agents and CI are instructed to judge pass or
fail from this script's exit status and nothing else, so a load-sensitive
verdict either trains people to re-run until green (which defeats the
gate) or produces false failures that get investigated as regressions. It
cost a real investigation in the run above.

## Design note

The verifier already carries a load-independent budget: deterministic work
units, enforced per tactic class (simple 500000, smart 2000000, control
2000000) and reported by `click profile`. Those are a function of the
input and the proof, not of the machine. The wall-clock limits are doing a
different job — catching a hang or a pathological blowup that no unit
budget bounds — so the fix is probably not to delete them but to separate
the two roles: deterministic units decide the verdict, wall clock stays as
a generous watchdog against non-termination, set far enough above the
observed worst case that ordinary load cannot reach it.

Whatever shape it takes, the acceptance criterion is that the verdict is
reproducible on a loaded machine.

## Intended regression

- A deterministic check that a fixture whose proof is unchanged produces
  the same gate verdict under artificial load (for example, the gate run
  with a CPU-saturating background job), demonstrating the verdict does
  not depend on available cores.
- `bubble_sort3_loop_permutation` specifically, since it is the observed
  case: its cost pinned as a deterministic unit budget rather than a
  wall-clock allowance.

## Acceptance criteria

- `scripts/check.sh` returns the same exit status for a given tree
  regardless of machine load, or every remaining wall-clock limit is
  documented as a non-termination watchdog with headroom stated against a
  measured worst case.
- The fixture harnesses report which limit a failure hit — deterministic
  budget or watchdog — so a timeout is never mistaken for a proof
  regression.
- This file and its Open-list line are deleted when the fix, its
  regression coverage, and any documentation land.
