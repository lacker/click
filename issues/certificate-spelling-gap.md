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

WORK IN FLIGHT at wind-up (2026-07-31 ~3:30 pm): an agent branch
`worktree-agent-a50a9739f4232cd94` holds active work on exactly this
(probing vector_fill cover spellings; last state: extending cover
candidates to effect facts). Check that branch before starting fresh.

Done when: the three mdtests de-quarantine and owned-string's frontier
moves.
