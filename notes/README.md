# notes/

Short-term working documents: the current plan, per-task workstreams,
and references for work in flight. Nothing here is durable
documentation — fold things into `docs/` or delete them as they finish.
Finished task files are deleted; their record is `git log -- notes/`.

- `plan.md` — **start here**: the project goal and the status board.
- `conventions.md` — how work happens: gates, multi-agent workflow,
  decision boundaries, working rules, settled invariants. Read before
  touching anything.
- `tasks/*.md` — ONE file per open work item, exactly (context,
  repro commands, done-criteria, and a `Claimed:` line). One agent per
  file at a time; keep your file current as you work — it is the
  handoff document.
- `regression-history.md`, `memory-dag.md`, `canonical-memory.md` —
  reference records behind the open tasks.
- `language-proposals.md` — surface-language proposals (parked; these
  are Surface Click semantics changes and need the owner).
