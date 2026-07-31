# Conventions — read before working on any task

Shared, rarely-changing contract for every agent working in this repo.
Task-specific state lives in `notes/tasks/*.md`; this file is about how
work happens.

## Gates — keep master green

Every change validates all three before landing:

```
cargo nextest run --lib --bins   # ~490 tests, ~5 s
cargo test --test mdtests        # ~10 s
cargo test --test examples       # ~11 s
```

`--lib` alone does NOT run the binaries' `#[cfg(test)]` modules — the CLI
tests went unexercised by the gate set until 2026-07-30. Always pass
`--bins` too.

Commit direct to master in small validated steps. Gate-validated work
merges to master without asking; ask before merging pre-existing
branches with unreviewed history or deleting branches/worktrees.

## Multi-agent workflow

- One task file = one workstream = one agent at a time. Before starting,
  set the `Claimed:` line in the task file (branch name + date) and
  commit it; clear it when you stop. If a task is claimed and its branch
  has recent commits, pick another task.
- Work in a git worktree when any other agent may be active
  (`.claude/worktrees/`); hand off via branches, not files.
- Write only to your task file plus the code you own; `plan.md` is a
  one-line-per-task status board — update your line only.
- Keep your task file current as you work: it is the handoff document.
  Record diagnoses, dead ends, and exact repro commands, not just wins.

## Decision boundaries (owner, 2026-07-30)

- Changes to the semantics of Surface Click need the owner's call.
- Certificate-format details and implementation internals do not —
  proceed ("let you cook").
- Long runs must surface slowness: state expected duration up front,
  alarm on stalls, and treat slow-but-passing as a reportable finding
  (click-audit enforces `--slow-site-limit` / `--time-limit`).

## Working rules

- Fix correctness bugs before continuing any sweep.
- Reproduce stale timing claims before acting on them.
- One frontier at a time; commit each independently verified fix.
- Probe pattern: env-gated eprintln/file dumps at the failing check,
  run with MDTEST_FILTER or a targeted click-verify, strip probes
  before committing.
- Guard and depth-gate any new recursive prover arm: three separate
  stack overflows in 2026-07-30 work traced to structural recursion on
  deep terms (harness children get 64 MB stacks as a backstop, not a
  license).
- SOUNDNESS TRAP: never drop havoc/call-havoc blocks from canonical
  load memories; kernel test
  `memory_load_equality_does_not_ignore_loop_havoc_identity` guards it.

## Settled design invariants

- TacticCertificate is the smart/simple boundary; a smart success must
  replay through a surface-expressible certificate before acceptance.
- Expansion emits the exact accepted certificate — no second proof
  search, no generic fallback.
- Simple tactics are deterministic replay and must be fast; don't hide
  a slow simple tactic by expanding an enclosing smart tactic.
- ProofSite + one-based PATH:LINE:COLUMN are shared by verification,
  profiling, expansion, auditing, and rewriting.
- click-expand emits a rewritten sidecar and does not reverify it;
  verification and auditing stay separate composable operations.
- Kernel Click has no textual syntax; all output is documented Surface
  Click accepted by the ordinary parser. Canonical struct spellings are
  `owner->field`, `(owner->pointer_field)[start..end]`, `object(owner)`;
  `load_*` / `byte_offset` are escape hatches only.
- CLI watchdogs must kill and reap their children.
- Everything the certifier consumes gets a surface spelling.

## Useful tooling facts

- `CLICK_TIMINGS=1` emits per-tactic and certification-phase timings
  (contract execution / contract claims / per-claim).
- `click-profile <path.md>` profiles one mdtest (or a directory of
  them); quarantine does not apply. Its TIME ACCOUNTING section gives
  the exclusive SIMPLE/SMART/CONTROL/certification split plus the
  unattributed remainder — a large remainder means uninstrumented
  machinery, not a clean proof.
- `CLICK_DISABLE_DECIDE_MEMO` / `CLICK_DISABLE_CERT_ARMS` bypass the
  decide memo and the 2026-07-30 certification arms for A/B.
- `CLICK_DISABLE_MEMORY_DAG` stops the named-memory-states arc from
  recording or reading memory derivations, restoring the pre-arc path
  exactly (`notes/tasks/named-memory-states-arc.md`).
- `MDTEST_FILTER=<name>` runs one mdtest; `CLICK_RUN_QUARANTINED=1`
  includes quarantined ones; `MDTEST_TIME_LIMIT=<secs>` bounds it.
- click-audit defaults: stop at first failure, 10 s slow-site limit,
  10 m run limit, resume via the printed `--start-at` command.
