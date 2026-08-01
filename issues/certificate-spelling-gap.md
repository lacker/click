# Certificate lowering gaps across memory snapshots

Certificate generation must name kernel facts in canonical Surface Click and
then replay exactly from those spellings. The 2026-07-31 repair now recognizes
folded predicate spellings under nested quantifiers, compares candidate loads
through the kernel's canonical load representation, and keeps the explicit
range and ordering premises needed to lower binder-local memory accesses.

Verified status (2026-07-31):

- `bubble_pass3_max_suffix` passes in 0.58 s and is no longer quarantined.
- `composite_resource_vector_fill_loop_snapshot` passes and is no longer
  quarantined; its independent deterministic `close_invariants` slowdown was
  fixed by caching repeated alias and derivation decisions during replay.
- `field_derived_precise_effect_after_metadata_write` still fails after about
  215 s on four effect-chain postconditions. No minimized derivation candidate
  is produced, so this is no longer accurately described as only a missing
  spelling for an otherwise-complete candidate. It also retains the independent
  slow fold in `field-derived-slow-fold.md`.
- `owned-string`'s certificate failures are fixed. Store certificates now
  retain their Surface Click spelling, replay can transport the resulting
  equality and loadability facts across the certified stores, and folding the
  final composite consumes the equivalent whole-range resource spelling
  instead of leaving subrange fragments. The project remains quarantined only
  because its complete gate exceeds the 10-minute budget; that independent
  performance problem is tracked in `owned-string-slow-proof.md`.

History: these are regressions from the 2026-07 certificate-strictness work;
bisect verdicts and the full experiment record are in git history
(`git log --all -- notes/regression-history.md`). The stopped worktree
`worktree-agent-a50a9739f4232cd94` remains historical evidence only. Its broad
uncommitted covering-loadability experiment was not copied; the applied repair
is narrower and replay-checked.

Done when: field-derived's effect-chain claims certify and this issue can be
deleted. The remaining deterministic performance bugs are tracked separately.
