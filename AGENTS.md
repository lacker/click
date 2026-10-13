# Working on Click

## Deliver through pull requests

Develop in a fork of `clicklang/click` and submit coherent, tested changes to
upstream `master`. Each task thread has at most one open PR: add subsequent
increments to it, without stacking PRs. After it merges or closes, start later
work from current upstream. Never push directly to `master`, merge directly,
or bypass required checks or the merge queue.

For authorized work with Lacker, request auto-merge immediately after creating
or updating the PR, then continue working without waiting for CI. Check queue
state before every follow-up push; do not push onto a head whose queue build
has started. After merging, verify all pushed commits reached upstream.

Read the [contribution workflow](docs/internals/contributing.md) before
publishing. It contains the queue procedure, fork/remote setup, and the limited
upstream task-branch exception for agents unable to push to a fork. Verify the
push destination rather than assuming `origin` is a fork.

## Isolate work and validate it

Use a dedicated task branch and worktree. Keep the shared primary checkout
clean; never overwrite unrelated changes or copy uncommitted work into it.
Update it only through Git after review. Use a separate throwaway worktree for
operations that move `HEAD`, such as bisecting. See the
[worktree procedure](docs/internals/contributing.md#worktree-and-integration-procedure).

Choose local checks appropriate to the change and report what ran. A full local
gate is not required before every PR; CI and the merge queue run it for code
changes. `scripts/check.sh` is the full green-tree verdict, not `cargo test
--lib`. Read the actual command's exit status; preserve it when piping output.
For prose-only changes, use `scripts/check.sh --docs-only`.

Preserve the gate's ten-minute budget. Keep slow audits and mutations in nightly
and add tests for distinct behavior, not duplicate coverage. Follow
[Testing Click](docs/internals/testing.md) for test selection, limits, and
expansion checks.

## File defects; ask before adding roadmap work

File reproduced verifier, tooling, or diagnostic defects in `bugs/` without
asking; tell the user what was filed. New `issues/` files and issue-list entries
require an explicit user request. A general request to investigate or implement
something does not authorize new roadmap entries. Do not disguise roadmap work
as a bug; report uncertain classifications to the user.

Follow [bug filing](bugs/README.md) and [issue filing](issues/README.md) for
reproductions, acceptance criteria, and cleanup when a fix lands.

## Keep `docs/` for AI readers; leave `guide/` to the maintainer

`docs/` is the AI reference: written for AI readers who use or develop Click
and maintained by agents. Keep it accurate, dense, and backed by checked
examples. `guide/` holds the human-written guide; agents do not create or edit
files under it. The maintainer writes it.

## Keep existing C as the verification boundary

Prove the existing program. Do not weaken claims or rewrite otherwise-correct C
into a shape the verifier prefers. Put adaptations in contracts, lemmas,
resources, tactics, lowering, or the kernel. This includes avoiding proof-only
locals, no-op branches, alternate control flow, and identifier changes that
merely evade verifier bugs.

Change C only for an independently desirable program change, an actual C bug
or undefined behavior, or a documented semantics-preserving translation into
supported C. Retain the original source pattern in regressions;
a simplified example is not evidence that the original pattern is supported.

## Use proof friction to improve the tool

When developing an example and the verifier together, apply the
[three-strikes rule](docs/concepts/proof-failure-triage.md#three-strikes-during-example-development):
after the second failure at the same obligation, run a focused proof trace and
explain what it reveals before another attempt. If it explains the failure,
use that information to correct the proof; tracing can be a sufficient remedy.
After the third failure, pause local variations and investigate using the trace.
Normally this pause should trigger a conversation with the user: explain the
evidence and proposed response before changing tooling. Tooling design changes,
including what diagnostics or traces show, require user approval. Reproduced
bugs in existing behavior may be fixed without approval; do not treat a proposed
presentation or workflow improvement as an automatic bug fix. Existing approval
for a specific improvement carries forward and need not be requested again.
Do not infer a verifier problem from repeated rejection before trying tracing.
A trace that leaves the necessary comparison unexplained may itself need
improvement. Investigation is required; a verifier change is not.

Stop affected feature work immediately for tooling defects: unexpected
slowness without a prompt local failure, unverifiable smart certificates or
expansion, disagreement between proof tools, unusable diagnostics, or irrelevant
proof bookkeeping needed to evade verifier behavior. Reduce and fix the defect;
if blocked, preserve a reproduction, report it, and leave a coherent checkpoint.
Do not raise limits or accept eventual success as a workaround.

A single prompt, bounded smart-search miss is expected. Try explicit relevant
steps; search completeness is not required. Follow
[proof-failure triage](docs/concepts/proof-failure-triage.md) to distinguish proof
mistakes, usability gaps, missing functionality, and bugs. Establish correctness
before optimization; do not expand an incomplete proof. After interrupted or
timed-out runs, confirm the verifier process tree exited before trusting timings.
See [Testing Click](docs/internals/testing.md) for the operational procedure.

## Keep verification scalable

Simple checking must scale with the selected source, explicit proof, and
relevant state delta, approximately linearly up to indexing factors. Do not
scan or clone unrelated environment, proof state, or history per step, eagerly
derive pairwise facts, or use deep structural cache keys on hot paths.
Smart-tactic expansion does not repair an expensive simple checker.

Performance-sensitive representation changes require deterministic scaling
regressions across multiple sizes; faster corpus timing alone is insufficient.
Follow the [verification efficiency contract](docs/internals/verification-efficiency.md)
for complexity requirements and review criteria.
