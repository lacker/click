# Soundness bugs found by the bug hunt

One `.md` file per confirmed or strongly evidenced soundness bug, parallel to
`issues/`: these are defects found by hunting, filed for the fixer rather than
for the roadmap. Each file states the violated invariant, a small intended
regression, and acceptance criteria. An accepted bug is deleted here when its
fix, regression coverage, and documentation land.

- [Contract retire keeps the zeroed reading](contract-retire-keeps-zeroed-reading.md) — machine-confirmed
- [store_union keeps a stale raw cell under an equal spelling](store-union-keeps-aliased-raw-cell.md) — machine-confirmed
- [spec-fold binder identities collide with the quantifier bands](spec-fold-binders-collide-with-quantifier-band.md) — structurally confirmed
- [Byte-extent residue comparison certifies wrapped loads](byte-extent-residue-compare-certifies-wrapped-loads.md) — statically confirmed
- [Footprint refusals drop fact-aliased writes](footprint-check-drops-fact-aliased-writes.md) — statically confirmed
- [The indexed loan route is bypassed through a proven-equal spelling](loan-index-is-bypassed-through-equal-spellings.md) — machine-confirmed
- [The owned-overlap rule misses cross-block pairs with proven equal bases](owned-overlap-rule-misses-alias-equal-pairs.md) — machine-confirmed
- [Spec-carrier substitution has no binder handling: capture and silent drops](spec-substitution-captures-and-drops-binders.md) — machine-confirmed
- [The loadable byte-offset route certifies a wrapped goal extent](wrapped-byte-extent-passes-loadable-bounds.md) — machine-confirmed
