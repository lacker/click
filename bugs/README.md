# Soundness bugs found by the bug hunt

One `.md` file per confirmed or strongly evidenced soundness bug, parallel to
`issues/`: these are defects found by hunting, filed for the fixer rather than
for the roadmap. Each file states the violated invariant, a small intended
regression, and acceptance criteria. An accepted bug is deleted here when its
fix, regression coverage, and documentation land.

- [The indexed loan route is bypassed through a proven-equal spelling](loan-index-is-bypassed-through-equal-spellings.md) — machine-confirmed
- [The owned-overlap rule misses cross-block pairs with proven equal bases](owned-overlap-rule-misses-alias-equal-pairs.md) — machine-confirmed
- [Spec-carrier substitution has no binder handling: capture and silent drops](spec-substitution-captures-and-drops-binders.md) — machine-confirmed
- [The loadable byte-offset route certifies a wrapped goal extent](wrapped-byte-extent-passes-loadable-bounds.md) — machine-confirmed
- [A union store leaves the other members' typed overlays stale](union-store-leaves-stale-member-overlays.md) — machine-confirmed
- [Entry-partition separation facts are never re-checked after equalities](entry-partition-separation-facts-unrechecked.md) — statically confirmed
- [The annotation quantifier counter is raised into other producers' bands](quantifier-counter-rises-into-other-producers.md) — statically confirmed
- [A ledger with an active hold is equal to its hold-free predecessor](hold-does-not-change-ledger-identity.md) — machine-confirmed
- [The storage-footprint check loses the write's byte width](write-footprint-check-loses-byte-width.md) — statically confirmed
- [The call-havoc retention's `local:` promise has no enforced boundary](call-havoc-local-retention-unenforced.md) — statically confirmed
- [The ordinary lend path binds a substitute occurrence](lend-binds-equal-looking-occurrence.md) — statically confirmed
- [The interface join erases a deallocation one arm performed](interface-join-erases-one-arm-deallocation.md) — machine-confirmed
- [An uncaught cpp throw skips every enclosing destructor](cpp-throw-skips-enclosing-destructors.md) — statically confirmed
