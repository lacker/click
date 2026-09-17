# Slice 2 is parked (2026-09-17)

This branch holds unfinished work on the fork/join slice of
`issues/concurrency-demo.md`. It is not green and must not be merged. It was
parked because `issues/termination-required.md` changes what a worker's
contract means: a join on a worker with no termination evidence may never
return, and Click's default is about to require termination. Resume only after
that issue lands.

## What is here

- `src/kernel/threads.rs`: `pthread_create` and `pthread_join` as kernel
  transitions. Creation runs the worker's verified rule at the spawn point,
  withholds the outputs in a suspension record, and mints a linear
  `joinable(handle, worker, argument)` token; join consumes the token and
  installs the outputs. A function may not return while it holds the token.
- Creation returns one successor with an untested result. That state is the
  failed creation and carries the successful state in `pending_spawns`; the C
  `if` on the result commits one, the way a null test commits a pending
  `malloc`. Only that `if` may run while a creation is pending. This keeps the
  surface unchanged: creation and join are `step()`, the split is `branch`.
- `docs/internals/threads.md`: the design record and the C11/POSIX basis.
- `drafts/spawn_minimal.md`: one worker, one creation, one join. It verifies
  with `execute(); simp();`. Move it back to `mdtests/` to run it.
- `drafts/fork_join_parallel.md`: the pinned two-thread probe. The worker
  verifies. The parent stops at the first join with "join after other
  stable-view activity in the parent is not supported yet": the second
  creation changed the loan ledger, and join requires the ledger it recorded.

## Known defects to fix on resume

1. `src/kernel/tests/thread_tests.rs` still expects creation to return two
   paths. Twelve of sixteen tests fail; rewrite the `created` helper to take
   the single pending path and resolve it under `result == 0` and
   `result != 0`.
2. Join compares the parent's loan ledger with the one recorded at creation,
   so two outstanding threads that both hold views cannot be joined.
3. If the worker's verified rule yields no return path, creation yields no
   successor at all, which would leave the parent's code after the creation
   unverified. Creation should depend only on the worker's prepared frame.
   Unconfirmed; check it first.
4. The proof of the minimal example has not been written with simple tactics
   only, and `click expand` has not been run on its `execute()`. Do both
   before trusting the design.
5. A parent cannot lend `&local` to a worker that `owns` it, because stack
   locals carry no ownership facts. The same is true of an ordinary call, so
   this is not a thread defect, but the pinned probe's job structs only work
   because the worker views them.
6. A function that declares `decreases` and joins a worker should require the
   worker's termination evidence. Not implemented.
