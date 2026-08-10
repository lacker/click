# Finish the bounded object-pool example

Build the practical bounded-pool example after its remaining independently
reduced blocker, `invariant-population-body-authorizes-c-access.md`, is green.
Resource-pattern transitions, decrement certificates, step expansion, and
marked-load transport now have focused passing regressions.

The preserved investigation is on local branch
`wip/bounded-pool-investigation` at commit `5154279`, with a worktree at
`/private/tmp/click-bounded-pool-wip`. It is evidence and reduction material,
not a patch to merge wholesale.

The final example should use one `pool_object(pool, object)` resource, a
copyable validity predicate equating `checked_out` with
`count(pool_object(pool, _))`, two simultaneous checkouts, object mutation,
reverse-order return, and empty-pool destruction. Do not reshape the C around
the verifier.

## Acceptance criteria

- Focused tests cover successful transitions, independent pools, zero, and
  capacity rejection before the full example is restored.
- The example verifies promptly using the direct CLI.
- Every remaining smart tactic expands and replays under audit.
- Its README explains the division between metadata ownership, validity
  knowledge, and transferable checkout resources.
