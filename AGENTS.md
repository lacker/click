# Working on Click

## Existing C is the verification boundary

Click exists to prove properties of existing C programs. Adoption in a large
codebase must not require refactoring working implementation code into a shape
the verifier happens to prefer. For C inside Click's supported semantics, a
true claim that cannot yet be proved is a Click language, model, or tooling gap.
It is not permission to weaken, specialize, reroute, or cosmetically rewrite
the C until the proof passes.

Treat C source as fixed when adding a sidecar or repairing a proof. Put the
adaptation in contracts, lemmas, resources, tactics, lowering, or the kernel.
In particular, do not add no-op branches, proof-only locals, redundant
assignments, specialized helper calls, or alternate control flow to expose a
friendlier proof state. Do not change identifier spellings to avoid a lowering
or snapshot bug.

A C change is in scope only when it is independently desirable as a program
change, fixes an actual C bug or undefined behavior, or is a documented
semantics-preserving translation into the currently supported C0 subset. Keep
the original source as the regression whenever verifier work exposes a gap.
Synthetic examples may be small, but they must not be presented as evidence
that Click handles an awkward source pattern that the example has edited away.

## Tooling stability comes first

Verifier and proof-tooling problems block feature and example work. Stop the
current feature when any of these occurs:

- verification is unexpectedly slow or crosses a tactic budget without a
  prompt, local failure;
- a smart tactic reports success but its certificate does not replay;
- `click expand` fails, emits an unverifiable rewrite, or disagrees with
  `click profile` or `click audit`;
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

Do not build Click workflows by recursively spawning Click commands, hidden
child modes, test-binary wrappers, stderr scraping, or shell redirect/move
recipes. CLI subcommands and fixture gates should call the shared bounded
verification engine directly. Keep OS process isolation only as a narrow,
owned crash-containment boundary.

This priority is deliberate: Click's examples and language features depend on
fast verification, replayable certificates, working expansion, and actionable
diagnostics. Building above a broken proof-tool boundary makes later failures
harder to interpret.

See `issues/README.md` for issue policy and
`docs/advanced/testing-click.md` for the performance and expansion workflow.
