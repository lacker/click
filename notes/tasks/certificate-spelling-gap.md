# Certificate lowering cannot spell snapshot-orphaned premises

Status: open — the new critical path (successor to
separation-containment-prover, landed 2026-07-31)
Claimed:

The prover work fixed owner_buffer (de-quarantined, 0.06 s) and proved
the remaining three members all fail in ONE subsystem that is not the
prover: certificate lowering's surface spelling —
`synthesize_surface_proposition` / `checked_surface_fact_at_outcome`
(src/lang/click/proof.rs, ~7600-7770 and ~13380-13530 as of 2026-07-31)
cannot spell premises whose loads reference snapshots that no retained
program point carries.

Evidence per member (measured by the prover agent, details in its
final task-file commit a8f9616 / notes/regression-history.md):

- **bubble_pass3** (0.47 s fail): the required ForAll is found
  kernel-identical among available facts (`fact == required` is true) -
  candidate selection is fine, spelling synthesis is the gap.
- **vector_fill** (41.5 s fail): `minimal_proposition_derivation`
  SUCCEEDS (proven via no CLICK_DERIVE_DUMP_DIR dump); the blocker is
  premise spelling, same class.
- **field_derived** (238 s fail): same site, now the "expressible path
  facts do not replay" spelling class.

Related member with the same smell, different site:
case-split-expansion-merge.md (the per-path merge). Check whether one
spelling mechanism serves both before building two.

Constraint carried over: whatever spelling is synthesized must be
canonical Surface Click accepted by the ordinary parser (settled
invariant), and `at(<point>, ...)` anchors only work for program
points the proof retains - the gap is exactly premises whose snapshot
is not any retained point, so the fix likely needs either a new
retained-point selection or a spelling through `old(...)`/DAG names.

Repro:
```
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=bubble_pass3 cargo test --test mdtests
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=vector_fill cargo test --test mdtests
```
(field_derived: 238 s to fail; bound it, confirmation only.)

Done when: bubble_pass3 and vector_fill de-quarantine; field_derived
moves or passes; ALSO retest example owned-string (bounded — it takes
5m26s to fail): its current frontier is this same class ("expressible
path facts do not replay the postcondition derivation") (its residual cost items live in
field-derived-fold-cost.md).
