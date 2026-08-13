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
