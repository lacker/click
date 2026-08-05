# Working on Click

## Tooling stability comes first

Verifier and proof-tooling problems block feature and example work. Stop the
current feature when any of these occurs:

- verification is unexpectedly slow or crosses a tactic budget without a
  prompt, local failure;
- a smart tactic reports success but its certificate does not replay;
- `click-expand` fails, emits an unverifiable rewrite, or disagrees with
  `click-profile` or `click-audit`;
- a normal diagnostic expands into a huge internal state dump; or
- an example needs unnatural C or irrelevant proof bookkeeping to route around
  verifier behavior.

Reduce and fix the tooling problem before resuming feature work. If it cannot
be fixed in the same coherent chunk, create a focused file in `issues/` with a
regression design and acceptance criteria, then restore the worktree to a green,
check-in-ready checkpoint. Do not silently work around the problem, raise time
limits, accept a slow successful run, or leave the only reproduction inside an
unverified example.

After any timeout or interrupted bounded command, confirm that its verifier
process tree exited before trusting later timing results. Stale workers are a
tooling failure, not background noise.

This priority is deliberate: Click's examples and language features depend on
fast verification, replayable certificates, working expansion, and actionable
diagnostics. Building above a broken proof-tool boundary makes later failures
harder to interpret.

See `issues/README.md` for issue policy and
`docs/advanced/testing-click.md` for the performance and expansion workflow.
