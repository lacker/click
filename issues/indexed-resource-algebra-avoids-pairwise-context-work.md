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

Scaling axes: `unrelated_resource_normalization_has_linear_deterministic_work`,
`adjacent_memory_normalization_has_linearithmic_deterministic_work`,
`disjoint_concrete_range_validity_scales_near_linearly`, and the fixed-candidate
resource lookup/consumption regressions isolate ambient resource count,
mergeable interval count, and relevant candidate count independently.

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

The same ordered interval index now narrows insertion into an already-valid
same-base concrete context to the duplicate interval and immediate neighbors;
it does not compare the new range with every existing range. Index
construction remains linear in the persistent context size and is included in
the deterministic regression.

The issue remains open for persistent incremental index updates, lazy
separation projection, and fixed permission-query gates over mixed symbolic
resources. In particular,
`observable_facts` still materializes pairwise separation propositions; that
must be replaced only together with indexed on-demand derivation so existing
certificates retain the same authority.

`Assumptions` now also maintains an incremental memory-separation index keyed
by the two base blocks. Pointer-disjointness replay selects only relevant
`CMemoryDisjoint` and memory `CResourceSeparate` candidates instead of scanning
every proposition. A regression holds one separation fixed while adding 128
unrelated propositions and checks that the candidate set remains one. The
owned-string integration profile shows that candidate selection is no longer
the only cost: several same-block symbolic candidates still require expensive
range-membership proofs. Indexing those ranges by stable base/interval
identity remains open.

Loadability propositions now have a separate incremental ordered index keyed
by the base pointer block. Direct loadability, structural subrange,
adjacent-range, and memory-resolution queries use only the relevant bucket
rather than filtering every proposition. Each bucket is a `BTreeSet`, so it
preserves exactly the candidate order of the former filtered global set; a
vector-backed prototype changed smart-search order and made
`owned-split-buffer` unstable, and was rejected. A regression holds one useful
subrange fact fixed while adding 128 loadability facts for unrelated blocks
and requires exactly one candidate. Derivation candidate selection remains
global until it can consume this index without changing its provenance search.

Direct resource-context equality now also consults the existing memory-block
and composite/token name-and-arity indexes before invoking proof-aware resource
matching. The comparator and its fallback semantics are unchanged, but a fact
is no longer compared with every unrelated fact on the opposite side. A fixed
candidate regression adds 128 unrelated token shapes and 128 unrelated memory
blocks and requires one candidate for each target. Same-shape symbolic pointer
comparisons remain expensive (notably `tree_rotate_left`); indexing removes the
ambient-resource multiplier but not that proof cost.

Definitional resource consumption now uses those same necessary-shape
candidates rather than falling back from exact lookup to every fact in the
resource family. A deterministic four-size regression consumes one token view
while adding unrelated token names and requires constant candidate work. For
memory resources, candidates are limited to the pointer block and ordered with
snapshot-insensitive matching bases first; the proof-aware algebra remains the
authority and all same-block candidates remain available as fallbacks.

Nested attribution also separates direct consumption, normalization, required
composite expansion, and available composite expansion. In the owned-vector
integration workload, the remaining `allocated_vector_push` containment cost
is three same-block symbolic range proofs, not candidate enumeration or
composite expansion. Establishing one assumptions memo-identity scope for the
whole representation certificate reduced that check from roughly 251ms to
205ms. Stable base/interval identities are still required to remove the
remaining range-proof cost.

Exact ownership-to-view satisfaction now uses `ResourceContext`'s existing
resource-key index. Return-resource core projection previously missed this
definitionally exact case and could send owned-memory cores through the
proof-aware snapshot/range comparator. Non-exact resource spellings still use
the proof-aware entailment path when an operation actually requires that
semantic judgment.

Return-resource transition profiling now separates lowering, composition,
expansion, core projection, and allocation checking. In owned-vector, core
projection dominates because a post-state `owner->data` view must be compared
with an older snapshot spelling. The comparison is semantically required: an
exact-only deduplication experiment left a stale view usable after its
allocation was freed in allocated-linked-list, and was rejected. The next fix
must accelerate or canonicalize that snapshot equivalence without retaining
both views.

General resource satisfaction now uses the same block/name-and-arity candidate
index for non-exact entailment and for its post-normalization retry. It no
longer scans every member of a resource family before entering the actual
proof-aware comparison. A four-size regression holds one non-exact memory
subrange query fixed while adding unrelated blocks and requires constant
deterministic work. The owned-vector profile confirms that the remaining
return-resource cost is inside 634 relevant indexed entailment calls (about
262ms), rather than unrelated-family enumeration; repeated same-shape
snapshot/range proofs remain the next boundary.
