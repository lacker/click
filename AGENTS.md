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
changes. `scripts/check.sh` is the budgeted test-configuration verdict; it combines
unit/API/proof fixtures in one `cfg(test)` build. Clippy, production and CLI
coverage run in `--nightly`. Bare `cargo test --lib` omits the gate feature and
proof fixtures. Read the actual command's exit status; preserve it when piping output.
For prose-only changes, use `scripts/check.sh --docs-only`.

Preserve the gate's ten-minute budget. Keep slow audits and mutations in nightly
and add tests for distinct behavior, not duplicate coverage. For expected timings
and cache-state comparisons, use the
[gate timing baselines](docs/internals/testing.md#gate-timing-baselines). Before changing
compiler flags, build profiles, or runners to speed up the gate, read
[what has been tried](docs/internals/testing.md#speeding-up-the-gate-what-has-been-tried);
prefer test-level work. Do not run the
nightly suite (`scripts/check.sh --nightly`, `CLICK_NIGHTLY`, or
`--run-ignored`) before a PR: it takes hours, and the nightly workflow runs it.
At most run the few nightly tests or fixtures the change plausibly affects,
by name, and say in the PR what was not run. Follow
[Testing Click](docs/internals/testing.md) for test selection, limits, and
expansion checks.

## Fix small defects; ask before filing bugs or roadmap items

Prefer to fix a small reproduced verifier, tooling, or diagnostic defect in
the same task thread: put its reproduction in the fix PR and land its
regression with the fix. `bugs/` holds internally discovered defects that are
not found through the proof-repair skill and are too large to fix now or
unrelated to the current work. Do not file one there without asking the user
first; describe it with its reproduction and ask whether to file it.
Defects found through the proof-repair skill go to GitHub issues after
user approval, including during internal development or nightly investigations.
Follow the skill's reporting instructions and labels.
Other defects reported by people or agents using Click also arrive as GitHub
issues. New `roadmap/` items require an explicit user request. A general request
to investigate or implement something does not authorize new roadmap items.
Do not disguise roadmap work as a bug; report uncertain classifications to the
user.

Follow [bug filing](bugs/README.md) and [roadmap filing](roadmap/README.md) for
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

## Define library interfaces in Click

A library the verified code calls, in any language, is seen only through the
interface Click defines for it: its types, what their values own, and its
functions' contracts. Never import, verify or re-implement a library's code,
and never special-case a library function or type in a front end beyond a
name-table entry. When a contract cannot express a library function, the fix
is a general contract feature, proposed to the user first. Use the
`library-interface` skill before adding or changing support for any library
function or type; the rules are in
[library interfaces](docs/concepts/library-interfaces.md).

## Use proof friction to improve the tool

When verification is slow, use the [`proof-optimization` skill](.agents/skills/proof-optimization/SKILL.md).

When comparing verifier runtime before and after a change, use the
[`benchmarking` skill](.agents/skills/benchmarking/SKILL.md).

When a proof fails, use the [`proof-repair` skill](.agents/skills/proof-repair/SKILL.md).
Follow the [proof repair procedure](docs/concepts/tracing.md): record the goal
that was not proved, write the argument as a chain of `have` goals, and refine
the first link that does not close until each link is one simple tactic.
Every attempt must change that chain. A new tactic, written form, or position for
the same link is not progress. Stop at one of its named outcomes. A link `close()` does not prove is too big, never by itself a
verifier problem. File defects found through this workflow as GitHub issues
after user approval, following the skill's reporting instructions, including
for `inexpressible-fact`, `contract-bug`, `obligation-bug`, `tactic-bug`, `internal-error`,
crashes, hangs, and confirmed diagnostic defects. An `unclear-output` outcome requires
independent evidence of a diagnostic defect before filing.
Do not put them in `bugs/`, even when discovered during internal development
or a nightly investigation. Explain the evidence and proposed response to the
user before changing tooling. Tooling design changes, including what
diagnostics or traces show, require user approval. Reproduced bugs in existing
behavior may be fixed without approval; do not treat a proposed presentation
or workflow improvement as an automatic bug fix. Existing approval for a
specific improvement carries forward and need not be requested again.
Investigation is required; a verifier change is not.

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
Scaling tests live in `src/scaling_tests/`, mirroring `src/`; read the ones
for the modules you touch, and run them all with
`cargo nextest run --lib -E 'test(/scaling_tests/)'`.
Follow the [verification efficiency contract](docs/internals/verification-efficiency.md)
for complexity requirements and review criteria.

[Verifier design](docs/internals/verifier-design.md) divides the verifier into
a fast part, which checks and may not scan, and a slow part, which searches and
must be expandable. Before proposing, implementing, or reviewing a change that
makes the verifier do more work, follow the `verifier-design` skill and start
the proposal with its design check.

## Construct valid proofs; never produce-then-check

Efficiency takes priority over a small trusted base
([trust](docs/concepts/trust.md)). A proof-object operation constructs its
successor directly and is valid by construction. Do not have the kernel
re-derive or re-validate what the same session just produced: no premise
re-walks, state re-comparisons, recomputed identities, or checker passes over
evidence a producer handed back. Do not cite trusted-base size, untrusted
callers, or defense in depth as a reason to add one. If a caller could supply
bad input, move that computation inside the operation instead of checking its
output. Where existing code or docs follow produce-then-check, treat it as a
defect to remove, not a pattern to extend. See
[construction, not re-validation](docs/internals/verification-efficiency.md#construction-not-re-validation).

## Follow the raise-lower principle

Every fact a proof state holds, and every goal it focuses, must raise to a
Surface AST that lowers back to it in the same context; expansion depends on
this. Raise from retained names and provenance, never by trying candidate
forms or historical states. Do not fall back to a placeholder, another
renderer, `None`, a skipped candidate, or a declining route. When raising a
fact is impossible, name the value where it is introduced or add its Surface
form, and treat the gap as a tooling defect. A new kernel fact or term form
ships with its Surface form. See the
[raise-lower principle](docs/internals/raise-lower-principle.md).

Keep the proof-visible program tree faithful to the target-language source.
Generated operations and typed temporaries belong to the source constructs
that cause them. When changing a frontend or lowering, check statement
selectors, diagnostics, and expansion replay. See
[proof-visible program structure](docs/internals/raise-lower-principle.md#proof-visible-program-structure).

Lowering is fact-stable: a term may depend on the program state and the
resources held, but facts may only refuse it, discharge its obligations, or
add side facts; they must not change the term produced. Do not fold, resolve
reads or aliases, pick comparison kinds, or prune disjuncts from facts during
lowering; put equality reasoning in checking (the e-graph). Check with
`scripts/audit.sh fact-stability`. See
[fact-stable lowering](docs/internals/raise-lower-principle.md#lowering-is-fact-stable).
