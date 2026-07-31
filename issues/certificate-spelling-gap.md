# Certificate lowering cannot spell snapshot-orphaned premises

The one remaining subsystem gap behind most quarantined tests.
`synthesize_surface_proposition` / `checked_surface_fact_at_outcome`
(src/lang/click/proof.rs) cannot spell certificate premises whose loads
reference snapshots that no retained program point carries — the fix
likely needs either retaining an additional program point or spelling
through `old(...)`/arena-named states, and output must stay canonical
Surface Click.

Gated on this, with measured evidence (2026-07-31):
- mdtest `bubble_pass3_max_suffix` (0.47 s fail): the required ForAll
  is found kernel-identical among available facts — candidate selection
  works; only spelling synthesis is missing.
- mdtest `composite_resource_vector_fill_loop_snapshot` (~42 s fail):
  `minimal_proposition_derivation` provably succeeds; premise spelling
  is the blocker. The needed loadable facts live in
  `replay.effect_facts`, not the certified-available set.
- mdtest `field_derived_precise_effect_after_metadata_write` (~238 s
  fail): same class ("expressible path facts do not replay").
- example `owned-string` (5m26s fail — see
  owned-string-loadable-bridging-slow.md): same message class, reached
  after the loadable-gap fix.

History: these are regressions from the 2026-07 certificate-strictness
work; bisect verdicts and the full experiment record are in git history
(`git log --all -- notes/regression-history.md`).

WORK IN FLIGHT, stopped at wind-up (2026-07-31 ~3:50 pm): branch
`worktree-agent-a50a9739f4232cd94` (worktree of the same name) holds
one committed increment — 72aab38 "Spell snapshot-orphaned ForAll
premises through the kernel's folded spelling" — NOT validated by
gates, plus an UNCOMMITTED mid-experiment tree (4 files: probes and a
cover-candidate extension pulling loadable facts from
replay.effect_facts). The agent's last finding before the stop: its
retry probe never fired, so the failing error is emitted by one of the
other `{proof_name} proof`-format sites (proof.rs ~9306 / 9451 / 9705),
not the site it had instrumented. Resume there; treat the committed
increment as a hypothesis until gates pass.

Done when: the three mdtests de-quarantine and owned-string's frontier
moves.
