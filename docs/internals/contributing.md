# Contributing to Click

This page is the contribution workflow for humans and agents: forks, pull
requests, the merge queue, worktrees, and where new work belongs.

## Fork and pull request workflow

Humans and agents contribute through a fork of
[clicklang/click](https://github.com/clicklang/click). Develop in your fork and
open a pull request against upstream `master` as soon as you have a coherent,
green, reviewable unit of work. Do not wait for a larger effort to finish; use
a draft pull request if more work is expected before it is ready to merge. This
also applies to maintainers with write or admin access: push development
branches to the fork, and integrate reviewed changes through pull requests.

The one exception is an agent session that cannot push to a fork, such as a
hosted sandbox whose credentials cover only `clicklang/click`. It may push its
own task branch to `clicklang/click`, never `master` or another contributor's
branch. It keeps at most one such branch per task thread, deletes it when the
pull request merges or closes, and removes any branch it left behind before
starting new work. Local agents and humans keep using forks.

Each task thread has at most one open pull request. Add all further coherent,
green increments to that PR, including unrelated fixes found along the way;
do not stack PRs. Once it merges or closes, start later work from current
upstream `master` on a new branch. Independent task threads may have separate
PRs.

For a new checkout, create a personal fork on GitHub, then run these commands.
Replace `YOUR_GITHUB_LOGIN` with the fork owner's login:

```console
git clone git@github.com:YOUR_GITHUB_LOGIN/click.git
cd click
git remote add upstream git@github.com:clicklang/click.git
git config remote.pushDefault origin
git config push.default current
git fetch upstream
git worktree add -b codex/your-change ../click-your-change upstream/master
cd ../click-your-change
```

Use `origin` for the fork and `upstream` for the organization repository. In an
existing checkout whose `origin` points to `clicklang/click`, rename that
remote to `upstream` and add the fork as `origin` before pushing. Verify both
destinations with `git remote -v`. The push settings above send ordinary
pushes to the fork even when a local branch tracks upstream. Agents use the
`codex/` branch prefix by default; humans can choose a descriptive branch name.

Perform edits, experiments, tests, and commits in the task worktree. Keep the
shared primary checkout clean. Follow the isolation and tooling rules in
[AGENTS.md](https://github.com/clicklang/click/blob/master/AGENTS.md).

Before submission, use judgment to choose focused local checks that fit the
change. A full `scripts/check.sh` run is not required before every PR; the PR
workflow runs the full gate for code changes, and the merge queue checks the
prospective upstream tree. For prose or documentation-metadata changes,
`scripts/check.sh --docs-only` is a useful focused check. Report which checks
ran, commit a coherent change, then push the task branch to the fork:

```console
git push -u origin HEAD
```

Open a pull request on GitHub from that fork branch to `clicklang/click`'s
`master`. Describe the problem, the resulting behavior, and validation. For
each follow-on increment on the same effort, run the relevant checks and push
the changes to this same branch so the existing pull request stays current. If
upstream moves, update the branch and rerun affected checks before merging.
After the pull request merges, fast-forward a clean local primary checkout from
upstream with Git; begin any later effort on a new branch and pull request.

Upstream `master` requires a pull request and a passing GitHub Actions `test`
check. The merge queue runs the full `scripts/check.sh` gate against the
prospective upstream tree, including the latest `master`, and merges one pull
request at a time only after that check passes. A passing pull request check
alone does not authorize a direct merge or push to upstream `master`.

### Lacker and agent merge-queue loop

This is the preferred path when Lacker is working with an agent authenticated
to GitHub as `lacker` and has authorized the agent to deliver the change.
Other contributors should use the normal PR and review process above.

1. Before follow-up work, inspect the branch's PR. If it remains open, keep
   working on that PR. If it merged, start a new PR for the new work.
2. Make a coherent change and choose local checks based on its risk and scope.
   A full `scripts/check.sh` run is not required before every PR; report which
   checks ran and let PR CI and the merge queue run the full gate.
3. Push to the contributor's fork and create or update the PR against upstream
   `master`.
4. Immediately request **Merge when ready**, even while checks are running, by
   running `gh pr merge <PR> --auto`. GitHub records the request and adds the
   PR to the merge queue once its requirements pass. Do not wait for CI to
   finish before requesting this. The repository's **Allow auto-merge** setting
   must be enabled; it is enabled on `clicklang/click`.
5. Once GitHub confirms the request, continue with the next work without
   waiting for checks or the merge to finish.
6. On the next update, inspect the PR again. If it merged, open a new PR. If
   it is open and not in the merge queue, push the new work to it and run
   `gh pr merge <PR> --auto` again. Pushing to a PR that is already in the
   queue does not remove it: the queue merges the head it was enqueued with,
   and later commits are left behind on the branch. So first check the
   queue entry:

   ```sh
   gh api graphql -f query='{repository(owner:"clicklang",name:"click"){pullRequest(number:<PR>){id mergeQueueEntry{id state}}}}'
   ```

   If its state is `QUEUED`, its final build has not started and nothing is
   wasted by resetting it: remove it from the queue (the `dequeuePullRequest`
   mutation with the pull request `id`, not the queue-entry `id`), push the
   new work, update the PR
   description, run `gh pr merge <PR> --auto` again, and confirm the queued
   head is the new one. If its build has started (`AWAITING_CHECKS` or
   later), or the new work is a large change on its own, leave the PR alone
   and deliver the new work in a new PR after it merges. After any PR merges,
   check that every commit pushed to it reached `master`.
7. If checks fail, a conflict appears, or GitHub removes the PR from the
   queue, resolve the problem, update the PR, and register the merge request
   again. Then continue with the next work.

If GitHub reports that auto-merge is not allowed, report the repository
setting as a blocker to the maintainer; do not wait for CI as a workaround.
Do not wait for optional human review on this fast path. Required review rules
still apply. Never use `--admin`, merge directly, or bypass required checks or
review rules.

The test workflow runs on pull requests, including those from forks. Fork
pull requests do not need repository secrets for the test gate; GitHub may
require a maintainer to approve an outside contributor's workflow run. Release
publishing uses version-tag pushes, so opening a pull request does not publish
a release.

## Worktree and integration procedure

Use a dedicated task branch and worktree for edits, experiments, tests, and
commits. Keep incomplete prototypes there and restore a coherent, tested
checkpoint before committing. Never copy uncommitted files into the primary
checkout or overwrite unrelated work.

After a PR merges, confirm every pushed commit is an ancestor of upstream
`master`. Update a clean primary checkout only by fast-forwarding with Git.
If unrelated changes or conflicts prevent that, stop and coordinate. When
upstream moves during development, update the task branch and rerun affected
checks. Choose local validation by scope as described above; PR CI and the
merge queue supply the full gate before upstream integration.

Run operations that move `HEAD`, such as `git bisect`, in a separate throwaway
worktree so they cannot disrupt an in-progress change or its saved patches.

## Implementing a change

Most Click changes should start from a proof need, not from an isolated syntax
idea.

The default workflow is:

1. Find the smallest nearby mdtest.
2. Add or change a test that shows the desired behavior.
3. Confirm the expected failure.
4. Implement the smallest parser, lowering, kernel, or prover change.
5. Add unit tests if the change is below the mdtest level.
6. Update the relevant reference entry and public-surface inventory.
7. Run focused tests and report them; PR CI and the merge queue run the full
   `scripts/check.sh` gate for code changes.

The feature playbook is the detailed checklist.

## Where new concepts belong

Prefer this order:

1. An ordinary Click definition in `stdlib/prelude.click`.
2. Deterministic proof support for a general pattern.
3. A new tactic if users need explicit control.
4. New syntax only when existing syntax cannot express the concept clearly.

This keeps the language smaller and makes kernel support more reusable.

## Contributor reading path

If you are changing Click itself, read:

1. [What Click proves](../concepts/what-click-proves.md), for the user-facing
   boundary;
2. the relevant [concept page](../concepts/index.md), for the mental model;
3. the relevant [technical reference](../reference/index.md), for the public
   contract;
4. the [feature playbook](feature-playbook.md), for the change workflow;
5. [Architecture](architecture.md) and [Kernel](kernel.md), for module and
   trust boundaries.

## Documentation ownership

`docs/` is the AI reference. It is written for AI readers: its "Using Click"
part for agents that verify code with Click, its "Developing Click" part for
agents that change Click. Agents maintain it. Keep it factual, dense,
source-backed, and consistent with the local [documentation style](../style.md).
Update the machine-readable inventory or fixture mapping whenever a public
surface changes. `docs/SUMMARY.md` assigns each page to one part and sets the
reading order. The rendered site's `llms.txt` and single-file bundle
`click-reference.md` are generated from it at build time and not committed;
each page's first sentence is its `llms.txt` description.

The human-written guide in `guide/` (in the repository root) is the
maintainer's. Agents do not create or edit files there.

## Working conventions

- Gate: `scripts/check.sh` is the full green-tree verdict, and CI runs the same
  script for code-affecting changes. Run it unpiped. It covers formatting,
  documentation, library and binary tests, mdtests, and examples, using
  nextest. For changes limited to prose or documentation metadata, run
  `scripts/check.sh --docs-only`; it renders and checks the documentation
  without running unrelated unit or verifier tests. `mdtests/` Markdown is
  executable proof input, so changes there require the full gate.
- Probe pattern: env-gated eprintln/file dumps at the failing check,
  run under a filter, strip probes before committing.
- Bound any new recursive prover arm by the inputs it walks: the term's
  structure, a strictly decreasing snapshot id, or a cycle check on the
  query. Never by a count or a depth cut, which turn a slow query into a
  wrong-shaped answer and defeat memoization. Structural recursion on deep
  terms has overflowed the stack before; the verifier threads carry the
  stack for it, and a scaling regression over several input sizes pins the
  bound.
- SOUNDNESS TRAP: never drop havoc/call-havoc blocks from canonical
  load memories; kernel test
  `memory_load_equality_does_not_ignore_loop_havoc_identity` guards it.
- Reproduce stale timing claims before acting on them; slow-but-passing
  is a reportable finding, not a resting state.
- Reproduced defects live in `bugs/`; user-approved roadmap work lives in
  `issues/`. Follow their READMEs when filing.
