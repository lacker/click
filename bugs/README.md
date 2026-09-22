# Soundness bugs found by the bug hunt

One `.md` file per confirmed or strongly evidenced soundness bug, parallel to
`issues/`: these are defects found by hunting, filed for the fixer rather than
for the roadmap. Each file states the violated invariant, a small intended
regression, and acceptance criteria. An accepted bug is deleted here when its
fix, regression coverage, and documentation land.

- [Contract retire keeps the zeroed reading](contract-retire-keeps-zeroed-reading.md) — machine-confirmed
- [store_union keeps a stale raw cell under an equal spelling](store-union-keeps-aliased-raw-cell.md) — machine-confirmed
- [spec-fold binder identities collide with the quantifier bands](spec-fold-binders-collide-with-quantifier-band.md) — structurally confirmed
- [Footprint refusals drop fact-aliased writes](footprint-check-drops-fact-aliased-writes.md) — statically confirmed
