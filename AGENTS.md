# Working on Click

## Work modes

The user may select a collaboration mode with a short declaration such as
`Day mode: ...` or `Overnight mode: ...`. The mode changes communication
cadence and autonomy, never correctness standards, source-fidelity rules, or
tooling-stability requirements. If no mode is declared, prefer day mode for
interactive work.

### Day mode

Work in one independently understandable chunk at a time and discuss findings
with the user frequently. Stop and check in before making a significant design
decision, broadening scope, or beginning a response to an unexpected tooling
problem. Preserve the failing case and a green checkpoint while waiting; do
not work around the problem. Optimize for shared understanding rather than
closing the entire task list quickly.

### Overnight mode

Continue autonomously for as long as useful, completing independent green
chunks with focused commits and pushes. Treat the requested task list as a
priority queue, not an obligation to force every item through. The declaration
authorizes ordinary commits and pushes for completed in-scope chunks, but does
not authorize unrelated work or destructive operations.

Tooling instability is a stop condition for the affected feature. Never route
around unexpected slowness, missed budgets, expansion/verification disagreement,
misleading diagnostics, enormous states, or pressure to reshape C or example
code. Do not raise limits, add arbitrary search caps, weaken examples, or
change C to make a proof pass.

If the underlying tooling fix is clear and bounded, fix it with a focused
regression, commit and push the green chunk, and continue. If it requires a
significant design decision, preserve a green checkpoint, write a detailed
issue with the reproduction and acceptance criteria, and move to another
genuinely independent task. Do not leave broken intermediate commits or
running verifier processes.

A prompt, bounded smart-tactic failure is not tooling instability. Smart
tactics are incomplete heuristics, and overnight work must not turn each hard
proof into a search-engine project. Split the proof into smaller operations or
use explicit simple tactics and continue. Investigate the engine only when
search misses its bound, produces misleading or enormous diagnostics, reports
success without a verifiable expansion, behaves nondeterministically, or the
needed proof cannot be expressed through the simple tactic surface.

At the end of an overnight run, report completed work, remaining issues,
important discoveries, and decisions that need discussion.

## Isolate work from the primary checkout

Unless already operating in a task-specific worktree, create a dedicated Git
branch and worktree before editing files. Perform implementation, experiments,
formatting, tests, and commits there. Treat the shared primary checkout as an
integration checkout, not a development workspace; do not expose other agents
to partially implemented or failing changes.

Integrate only a coherent green commit. Before integration, run the relevant
focused and full gates in the task worktree, verify that the primary checkout
is clean, and confirm that its base has not moved unexpectedly. If the base did
move, update the task branch and rerun any affected gates before integration.
Move the tested commit into the primary branch with Git rather than copying
uncommitted files. Never overwrite unrelated changes in the primary checkout;
stop and coordinate if it is dirty or integration conflicts.

Keep failed prototypes and incomplete investigations confined to their task
worktree. Restore or replace them with a green checkpoint before committing,
and do not merge or push them to the primary branch. These rules apply in both
day and overnight mode.

Run long-running Git operations that move `HEAD`, such as `git bisect`, in a
throwaway worktree rather than the one holding the change. Bisecting in place
leaves the task worktree on an unrelated commit and turns a routine stash pop
into a conflict against the wrong base.

## Judge green from `scripts/check.sh`

`scripts/check.sh` is the gate, and CI runs exactly that script so the two
cannot drift. Decide pass or fail from its exit status.

Never decide from piped `cargo test` output. A shell pipeline reports its last
command's status, so `cargo test | tail` exits 0 while the suite is failing;
this is how a broken mdtest survived 54 commits undetected. Piping is fine for
reading output, but the verdict comes from an unpiped run. The default `cargo
test --lib` is also not the gate: it passes while both proof-fixture gates
fail.

## File issues as one markdown file each in `issues/`

Any problem worth tracking becomes one kebab-case `.md` file in `issues/`
plus a one-line entry in the Open list in `issues/README.md` — bugs, design
gaps, and deferred work alike, not only tooling failures. State the violated
invariant, a small intended regression, and acceptance criteria, written so
a fresh agent can act on the file alone without the conversation that
produced it. Delete the file and its list line when the fix, its regression
coverage, and any documentation land.

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
- a smart tactic reports success but its generated certificate does not verify;
- `click expand` fails, emits an unverifiable rewrite, or disagrees with
  `click profile` or `click audit`;
- a normal diagnostic expands into a huge internal state dump; or
- an example needs unnatural C or irrelevant proof bookkeeping to route around
  verifier behavior.

Smart-search failure is expected when it is prompt, bounded, and actionable.
It is not a reason to stop feature work or modify shared heuristics. Prefer a
smaller smart tactic or an explicit sequence of relevant simple steps. Search
completeness is a non-goal; sound certificate validation, enforced bounds, useful diagnostics,
and sufficient simple tactics are requirements.

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
fast verification, checkable certificates, working expansion, and actionable
diagnostics. Building above a broken proof-tool boundary makes later failures
harder to interpret.

Establish correctness before performance optimization. Run ordinary
verification first; when it reports a prompt proof failure, repair that proof
before profiling or expanding it. Profile a non-verifying target only when a
timeout or unexpected slowness is itself the tooling problem being diagnosed,
and treat that result as an incomplete diagnostic frontier, not an
optimization profile. Never expand a tactic from an incomplete run.

See `issues/README.md` for issue policy and
`docs/concepts/proof-failure-triage.md` for failure classification, and
`docs/internals/testing.md` for the performance and expansion workflow.

## Scalable verification is a correctness requirement

A project written entirely with explicit simple tactics must verify in work
approximately linear, up to logarithmic indexing factors, in the selected C
source, Click source, and certificate. A simple tactic may do work
proportional to its explicit input, the affected C operation, and the proof
state or certificate delta it produces. It must not scan or clone unrelated
project-wide or path-wide state.

Do not introduce complete-environment clones per function, complete-state or
history clones per tactic, linear exact-premise searches, eager pairwise
derived facts, or caches keyed by deep structural comparison on a verifier hot
path. Smart-tactic expansion removes search; it is not a remedy for a slow
simple checker.

Performance-sensitive representation changes require deterministic scaling
regressions over multiple input sizes. A fixed corpus timing or a faster warm
run is supporting evidence, not proof of acceptable asymptotic behavior. The
canonical complexity contract, output-sensitive exceptions, and review rules
are in `docs/internals/verification-efficiency.md`.
