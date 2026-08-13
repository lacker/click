# Resource contexts materialize and rescan pairwise relationships

`ResourceContext` is a vector. Validity checks compare resource pairs,
observable facts eagerly produce cross-family separation pairs, exact
consumption searches linearly, and normalization restarts a nested pair scan
after each merge. Depending on merge shape, one operation can be quadratic or
cubic in the ambient resource count.

This violates the simple-tactic contract for `observe`, `unfold`, `fold`,
`frame`, statement permission checks, and contract resource certification.
Some operations must visit the members of the named resource, but they must not
enumerate unrelated resource pairs.

## Required design

Index resources by family, authority mode, base identity, and interval or
composite key. Validate new ownership incrementally against only potentially
overlapping entries. Represent separation as a consequence of indexed
authority and disjoint ranges; materialize an explicit proposition only when a
certificate asks for it. Normalize memory intervals with an ordered interval
structure instead of restart-based pair merging.

Preserve counted ownership, views, residual consumption, composite resources,
and symbolic-range reasoning. The new indexes are proof accelerators, not new
semantic authorities.

## Regression design

Scale unrelated token/composite resources, disjoint memory ranges, adjacent
mergeable ranges, and one fixed permission query independently. Include a
linear-output case that explicitly observes every named member and a fixed
query that must not emit all pairwise separations.

## Acceptance criteria

- Inserting or querying one resource touches only its indexed candidate set.
- Disjoint concrete ranges do not produce an eager quadratic proposition set.
- Normalizing `R` ordered adjacent ranges is `O(R log R)` or better.
- Fixed resource tactics pass the resource-count scaling gate.
- Resource validity and consumption regressions remain semantically unchanged.

## 2026-08-13 progress

`ResourceContext` now maintains exact, family, resource-shape, memory-block,
and endpoint indexes. Exact lookup is index-only, normalization selects
same-resource or adjacent-endpoint candidates instead of restarting an
all-pairs scan, and the default kernel regressions guard exact lookup,
unrelated normalization, and adjacent merging.

Validation of an existing context now recognizes the common same-base,
constant-interval case and uses an ordered sweep. A four-size deterministic
regression covers disjoint concrete ranges, so adding more unrelated ranges
cannot silently restore the former quadratic validation curve. Symbolic or
provably aliased bases still use the proof-aware pair checks.

The issue remains open for incremental insertion, lazy separation projection,
and fixed permission-query gates over mixed symbolic resources. In particular,
`observable_facts` still materializes pairwise separation propositions; that
must be replaced only together with indexed on-demand derivation so existing
certificates retain the same authority.
