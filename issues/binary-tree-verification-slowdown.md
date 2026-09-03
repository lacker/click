# Binary-tree verification exceeds the CLI limit since the binder-hygiene commit

## Status

Filed 2026-09-03 from the per-example timings in the landing gates of
`simplify-kernel.md`, and bisected the same day. The gate at `8bfa40fa`
already showed it (binary-tree 209 s while arena took 1 s and
owned-vector 10 s); it was misread as machine load. Nothing in the
`simplify-kernel` landings changes the timing: the branch and master are
identical on it.

## Violated invariant

Harness times do not rise, and every corpus example verifies under the
CLI's default limit: `click verify` gives each sidecar 30 s.
`examples/binary-tree/binary_tree.click` verified in 3 s before
`5e8882cf` ("Harden binder hygiene in kernel and surface proofs",
merged at `5852bcee`) and fails the limit after it with "verification
budget exhausted inside outer wall-clock deadline while running
verifier-core phase". The examples harness runs without tactic time
limits and stays green while spending 130–290 s on this one project, so
the failure is invisible to `scripts/check.sh` unless the per-project
`verified in` lines are read.

## Evidence

`/usr/bin/time -p click verify examples/binary-tree/binary_tree.click`
with a binary built at each commit in a throwaway worktree
(`git worktree add --detach`, `cargo build --manifest-path`), run back to
back on one machine under load averages of 7 to 28:

| commit | what it is | time |
| --- | --- | --- |
| `6dee2d5c` | master before the merge | 3.0 s |
| `a01bf4c8`, `a433946b`, `3ff322c9` | the master side of the merge | 7.3 s, 5.4 s, 6.7 s |
| `5e8882cf` | binder hygiene, on its base `3bafd1ca` | fails at 30 s |
| `5852bcee` and every later commit tried (`921c236b`, `097a184d`, `8837845d`, `8bfa40fa`, `ee2fd807`, `ebe4ea1f`) | | fails at 30 s |

`click profile` on master (cut at its own 30 s deadline, so a diagnostic
frontier, not an optimization profile): tactic time is 2 s in total;
contract symbolic execution takes 22–28 s over 7 calls, almost all of it
one call, the contract certification of `tree_sum_root_and_children`;
memory range coverage (fact range) 145 calls, 22–28 s; resource
satisfaction (indexed direct entailment) 164 calls, 19–27 s; fact range
coverage (shifted base relation) 145 calls, 14 s. The function observes
three `tree(...)` predicates, is `immutable`, and has three `requires`
per child field.

`5e8882cf` changes `src/kernel/reasoning/substitution.rs` (+677 lines),
`src/kernel/api/contract_certification.rs`,
`src/kernel/api/contract_certification/contract_claims.rs`,
`src/kernel/functions.rs`, `src/kernel/primitives/memory_state.rs`, and
`src/kernel/assumptions/proposition_reasoning.rs`, with regressions
`mdtests/composite_resource_fold_*`,
`mdtests/pure_induction_rejects_captured_binder.md`, and kernel
contract-execution and proof-reasoning tests that must keep passing.

## Intended regression

A deterministic scaling regression, in the kernel's work units rather
than wall time (`docs/internals/verification-efficiency.md`), for
contract certification of a function that observes `n` predicates over
`n` distinct child pointers with bound requires on each, for `n` of 1,
2, 3, and 4, pinned to grow linearly in `n`. The examples harness keeps
printing per-project times; a review reads them.

## Acceptance criteria

- `click verify examples/binary-tree/binary_tree.click` completes under
  the default limit, and the harness's `verified in` line for
  binary-tree is within 2× of the pre-merge 3 s on an unloaded machine.
- The cause inside `5e8882cf` is named and removed without weakening the
  binder-hygiene checks it added; its tests stay.
- The scaling regression above is in the unit suite.
- A profile of binary-tree shows contract symbolic execution and memory
  range coverage as fractions of a few seconds, not 20 s each.
