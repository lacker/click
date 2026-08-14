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

Observable memory separation now omits facts that the kernel can prove from
the range constructors alone. Owned ranges are grouped by pointer block; a
bucket sharing one concrete base is recognized in one pass, and distinct
blocks are never cross-paired. Thus contexts of disjoint concrete intervals or
distinct allocation blocks project no quadratic separation set. A four-size
deterministic regression covers both shapes and checks that an arbitrary
first/last separation remains provable without a materialized premise.

The issue remains open for persistent incremental index updates, complete lazy
separation projection, and fixed permission-query gates over mixed symbolic
resources. Abstract token/composite ownership no longer materializes pairs:
one internal `CResourceComposition` carrier is stored outside the ambient
proposition set, and direct separation queries use the resource indexes.
Symbolic same-block memory buckets still materialize proof-dependent pairs
until every certificate consumer can request the needed consequence lazily.

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

Compact composition authority now also serves the shallow memory-range,
pointer, alias-contradiction, and write-invalidation paths. Writes attach the
current state's compact resource observation directly, so correctness no
longer depends on a caller preserving an internal carrier in a vector of
surface-spellable facts. A regression retains only the compact carrier, relates
two pointer spellings through exact shallow equalities, and proves both pointer
and range/pointer separation without a materialized pair.

A full no-memory-pair experiment is now a precise three-part frontier. First,
post-execution surface certificate planning can use the compact authority to
solve its goal but cannot yet spell the requested separation consequence as a
simple certificate premise. Second, call-havoc/resource-representation
certification still loses enough separation evidence to report differing
memory snapshots and folded resources. Third, one modular call-snapshot replay
falls from its direct certificate path into much more expensive smart search.
The final deletion should therefore add one proof-producing on-demand
projection shared by certificate planning and representation replay; widening
snapshot-aware pointer search globally was measured, crossed the deterministic
smart-work budget, and was rejected.

A further instrumented pass eliminates two more candidate explanations and
narrows the certificate question to routing. At the failing `box_set`
post-execution goal `owner->data[old(owner->value)] == value`, the planning
`available` set does carry the compact composition (so assumptions built from
it can project separations), and every selected premise — including both
resource-declared separations — passes `pure_fact_is_replay_available`. The
failure is that the last-resort named-rule cascade in post-execution
simplification cannot spell an indexed-load store transport from those
premises. With pair emission enabled the same goal never reaches that cascade
at all: some earlier certification route consumes an emitted pair and
succeeds before the fallback runs. Closing the frontier therefore starts by
identifying which planner certifies this goal when pairs are present and what
premise shape it requires; the missing piece is that route's requirements,
not premise availability, spellability, or prover strength.

The pairs-present certification route for the failing `box_set` goal is now
fully traced. The claim never reaches outcome-simp lowering, the grouped
transition, or the exit-claim discharge: it closes during execution, through
`check_function_claim` over `path.execution_facts()`, because the executor's
automatic post-store fact transport placed
`owner->data[old(owner->value)] == value` at the frontier. That transport's
write-disjointness reasoning is the true pair consumer. Without pairs the
transported fact never appears, the claim stays open to the outcome, and the
fallback cascade has no vocabulary for an indexed-load store transport — the
downstream symptom, not the cause.

One wiring hypothesis is already falsified: extending the carrier fallback in
`pointers_proven_disjoint_by_shallow_explicit_range` with the same
fact-graph containment the pair-fed arm uses does not recover the transport,
so the executor's store-transport disjointness runs through a different call
one level deeper. The next session should probe which disjointness entry
point the post-store transport machinery invokes for the surviving-fact
decision and give that call the composition fallback with fact-graph-aware
containment; the `box_set` goal needs `old(owner->value) == 0` to place the
stored cell inside the owned `data[0..1]` range, so structural containment
alone cannot serve it.

A working prototype of the final deletion now exists on the local branch
`claude/lazy-separation-prototype` (commit ca2b1720). It deletes same-block
pair emission and instead serves `memory_separation_candidates` from an
incrementally maintained index projected from the compact compositions —
entries identical to the former pair propositions, maintained like the
existing separation-fact index, never materialized into ambient proposition
sets. Under that prototype the owned-string frontier case — formerly the
worst, falling into thirteen-plus seconds of smart search — verifies without
pairs, and the focused projection regressions pass.

Two frontier tests remain red on the prototype, with several explanations
measured and eliminated rather than guessed: projected bucket sizes stay
small, candidate multiplicity is not the cost, per-query prover fallthrough
was repaired by chaining projected candidates into the separation prover's
fact branch, and a per-query deep pointer projection plus memoization was
built, measured too expensive, and removed. What remains is that
`box_pipeline` exhausts its deterministic smart budget replaying a
user-written rewrite script, and vector-storage representation certification
still reports differing memory snapshots.

The box_pipeline blocker is resolved. Certificate-construction attribution
traced its cost to the ambient rewrite harvest, and the landed
premise-pairs-first ordering collapsed that tactic from over two million
units to under one hundred thousand (see
atomic-derivation-returns-premises-not-steps.md for the underlying design
gap). On the rebased prototype branch
`claude/lazy-separation-prototype-rebased`, two of the three frontier tests
now verify without pair facts; only vector-storage representation
certification remains, failing as before with "memory snapshots differ,
missing owns nonempty_buffer(owner)". The final investigation is why folding
a composite body loses snapshot evidence without materialized pairs — the
one consumer whose failure was never budget-related.

That investigation is now cell-precise (prototype commit 851fde96). The
representation certifier's three gates were probed individually: values and
resources pass; the memory gate fails, and inside it the definitional
cell-by-cell walk fails on pointer and value equalities between two
spellings of the same cells — one side resolved to concrete or entry-load
forms, the other left as nested symbolic snapshot loads. Adding the
proof-aware composition fallback to the memory-ranges disjointness variant
(mirroring the landed pointer-variant fix) did not change the outcome,
which eliminates the comparison-side hypothesis: the pair facts' remaining
load-bearing effect is upstream, in the executor's memory resolution, which
resolved loads while building the certified snapshots when pairs were
present and leaves them symbolic without them. The next session should
probe which executor-side resolution call produces the differently spelled
cells — comparing the certified snapshots' cell spellings with pairs on and
off will name it directly — and give that call the composition fallback.
The final comparison machinery needs no further work.

Budget-exhaustion diagnostics now attribute their work, and bracketing with
them reframed the box_pipeline blocker before its resolution: the same `have` replay costs between
1.0 and 1.9 million units on the current tree with pairs present — half to
nearly all of its two-million smart budget — so the prototype's marginal
per-statement index work tips an already-heavy tactic over the line rather
than introducing new asymptotic cost. The attributed failure shows all but a
thousand units inside one `grouped proof tactic replay` span with no finer
spans beneath it. The productive order is therefore: first add named spans
inside grouped proof replay and attribute the existing 1.9-million-unit cost
on the current tree, fix that, and only then re-run the prototype, which
will have budget headroom and one remaining representation question.

Re-running that experiment against the current tree corrects the design in
one important way: the kernel-side projection already exists.
`compact_composition_projects_symbolic_separation_without_pair_facts` proves
symbolic subrange separation from carrier-only assumptions with zero pair
facts through the existing composition branch of the separation prover, so no
new kernel proof object is required. The three failures reproduce exactly,
and instrumenting them shows their separation queries run against assumptions
whose composition set is empty: certificate planning and replay build many
small proposition-list contexts (for example inside
`append_simple_proof_step_for_operation`), the internal carrier is not a
surface-spellable proposition, and only the former pair facts rode along in
those vectors. The remaining work is therefore not prover strength but
carrier attachment: the consumer sites that construct assumptions while
holding a `CState` must attach that state's compact composition, the way the
write-invalidation path already does, and derivations that consume a
projected separation must record the projected `separate(...)` proposition as
provenance so certificate premise spelling and replay agree.
