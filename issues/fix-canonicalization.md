# Make canonicalization genuinely canonical

## Violated invariant

For a fixed term representation, canonicalization produces one deterministic
normal form. In particular:

```text
canonical(canonical(term)) == canonical(term)
```

Terms that are equal by Click's definition of representational or definitional
equality have the same canonical form. The result is independent of ambient
proof facts, proof-search order, numeric fuel, and the caller that requested
it. Canonicalization traverses its complete explicit input, uses an iterative
implementation where Rust stack depth is a concern, and has work proportional
to the input and output it names.

An equality established by a premise is not definitional equality. It belongs
in a context-local equality index or an explicit rewrite derivation; it must
not silently redefine global term identity. Rewriting a term through proved
equalities may be useful, but that operation is not canonicalization and must
retain the authority for each rewrite.

The current code uses "canonical" for three different operations. One is the
intended assumption-free canonical form. The other two mix contextual
simplification, equality-class traversal, memory resolution, and theory-aware
key construction. Those contextual operations have literal iteration/depth
limits and are not guaranteed to be idempotent. The naming obscures both the
proof boundary and the reason an answer can change at an opaque limit.

## Three concepts that must remain separate

### 1. Canonical form

`crate::kernel::eval::canonical_term` and its pointer-offset analogue are the
intended canonical representation. As documented in
`docs/internals/canonicalization.md`, this operation is assumption-free. It
removes representational memory differences by resolving recorded cells,
restricting unresolved snapshots to what a load can observe, finding the
cell's memory-DAG epoch, and replacing remaining loads with their stable load
variables.

This is allowed to determine term identity because its rewrites are justified
by the memory representation itself, not by a proposition selected from the
current proof context. It must be deterministic, total over supported finite
terms, and idempotent.

### 2. Equality indexing

A `PureFactContext` records propositions proving that canonical terms are
equal. Its equality graph may answer whether two terms are in the same proved
class, retrieve an exact equality path, or index facts under a class identity.
That identity is scoped to the particular fact context. It is evidence-backed
reasoning, not global term identity.

### 3. Contextual rewriting or lowering

Some producers want to express a value in a vocabulary that will remain useful
later. The motivating case is a verified call's mutable memory footprint: a
postcondition may spell an endpoint as `new_len`, while an entry-state equality
relates it to `old_len + 1`, and another equality may reduce `old_len` to a
constant. Rewriting the footprint can make later syntactic frame matching
work.

That transformation consumes proved equalities. It should therefore be named
as contextual lowering and either carry explicit rewrite evidence or remain a
narrow, clearly justified kernel operation over exact named facts. It must not
be presented as the canonical form of `new_len`.

## Current behavior

### Assumption-free canonicalization

`canonical_term` is a fixed composition of structural load canonicalization
and load-variable replacement. Existing tests cover a representative
idempotence case, and the documentation claims determinism and idempotence.
However, proposition reasoning skips deep structural canonicalization whenever
`bitvector_term_deeper_than(term, 64)` is true. Consequently the proof result,
though not the canonicalizer's nominal definition, still depends on an opaque
term-depth check. The recursive implementation of
`canonicalize_atomic_loads_deep` is the underlying stack-safety concern.

This issue owns that preflight limit. The canonicalizer must become safely
applicable at every supported finite depth, and its idempotence contract needs
multi-shape and multi-depth regression coverage rather than one representative
load case.

### Context-dependent footprint lowering

`PureFactContext::lower_bitvector_under_assumptions` in
`src/kernel/assumptions.rs` was added as a prototype for lowering memory
footprints at creation. It currently runs three alternating rounds:

1. `simplify_bitvector_under_assumptions` recursively simplifies the term,
   including constant equalities and constructor reductions.
2. `lower_bitvector_via_recorded_equalities` walks recorded equality edges,
   simplifies class members, and chooses a preferred term.

The preference puts constants first and then minimizes the number of embedded
memory loads. Despite having a total tie-breaker available, it deliberately
adopts a different representative only when doing so strictly lowers the load
count or changes a nonconstant into a constant. Same-load-count equal terms
retain their input spelling so existing consumers can reproduce recorded
vocabulary. Thus even two members of one proved equality class are not
guaranteed to produce one representative.

The two transformations do not commute, but the three-round loop is not the
effective bound it first appears to be. The equality worklist simplifies every
vertex it visits and adds that result to the same worklist. A selected whole
term can therefore expose a child simplification, enter another recorded
equality component, and repeat without consuming another outer round. An
eight-layer adversarial chain reaches its final constant in one such phase.
The outer loop merely reapplies the preference-gated result and is not a bound
on either equality/simplification alternation or work.

This explains why the obvious “more than three layers” counterexample does
not make a second call progress further. It is not a general idempotence proof:
the contextual simplifier includes constructors such as fold instantiation,
and the representative-selection rule intentionally refuses same-load-count
nonconstant vocabulary changes. The precise current contract is therefore a
visited-set worklist closure over exact generated terms, followed by a
preference-gated extraction, with up to three reapplications. That is a search
operation, not canonicalization, whether or not all currently reachable terms
happen to stabilize after one public call.

There are broader boundary and scaling concerns hidden inside the first step:

- `simplify_bitvector_under_assumptions` calls the general condition decider
  when it encounters an `if`, so contextual range lowering can enter more than
  local constructor simplification and exact equality lookup.
- `bitvector_constant_from_direct_equalities` currently scans
  `condition_facts` while following equality links. Repeating that work through
  a term or equality component can depend on unrelated ambient state rather
  than only the selected equality evidence.
- `lower_bitvector_via_recorded_equalities` generates simplified terms
  while walking one equality component and may thereby reach another
  component. Its visited set prevents revisiting an exact term, but does not
  cap the generated closure at twice the original recorded class size. The
  former comment claiming that bound was incorrect.

The direct callers are narrow:

- `lower_memory_range_under_assumptions` is called only from the verified-call
  rule, after a contract mutable segment has been evaluated and its facts have
  entered `effective_assumptions`. It lowers the base offset and both bounds.
  The result is used both to construct `CMemory::with_call_memory_havoc` and to
  record the call's `CMemoryEffectSummary`. Those copies must stay identical,
  preserve block and element width, remain equal to the evaluated segment
  under the exact entry facts, and retain a vocabulary that later write-set,
  disjointness, and frame queries can match. Resource-segment evaluation is
  upstream of this call; it is not another direct caller.
- `lower_pointer_under_assumptions` is called only by
  `load_variable_congruence_neighbor`; its offset helper is otherwise private
  to range and pointer lowering. The neighbor is consulted from both sides of
  `bitvector_terms_equal_from_facts`' equality-graph walk. It must preserve the
  memory snapshot and base block, and may connect load variables only when the
  address equality is justified by the facts in the current context.
- `lower_bitvector_under_assumptions` has no other production caller. Direct
  uses outside those two paths are characterization tests.

`simplify_bitvector_under_assumptions` has many other callers. This issue does
not assume that the general simplifier can simply be deleted; it requires that
canonical identity and contextual footprint lowering stop depending on its
search-capable behavior.

### Stage 2 deterministic-work characterization

Test-only counters measure actual contextual simplifier calls, full-fact
visits made by direct constant-equality lookup, equality-worklist vertices,
and outer rounds. The regression uses raw terms so eager constructors cannot
erase the intended shape. Current results are deterministic:

| input axis | sizes | simplifier visits | equality vertices | direct fact visits |
| --- | --- | --- | --- | --- |
| raw addition depth, no facts | 8 / 16 / 32 | 34 / 66 / 130 | 1 / 1 / 1 | 0 / 0 / 0 |
| direct equality-path length | 4 / 8 / 16 | 6 / 10 / 18 | 5 / 9 / 17 | 120 / 720 / 4896 |
| unrelated facts, fixed depth 8 | 8 / 16 / 32 | 34 / 34 / 34 | 1 / 1 / 1 | 144 / 288 / 576 |

All samples finish in one outer round. Structural traversal is linear in term
depth, and the equality worklist visits one vertex per class member. The
hidden cost is `bitvector_constant_from_direct_equalities`: it scans the whole
fact map for every term in its own equality walk, and contextual lowering calls
it again for every equality-worklist vertex. For a path of length `n`, the
measured fact visits are exactly `n(n + 1)(n + 2)`, cubic in this deliberately
simple shape. Unrelated facts also multiply the number of nonconstant term
visits even when they cannot affect the result.

This is the stage-2 design constraint for stage 4: replacing the outer
three-round loop alone would not remove the search or scaling problem. The
replacement must use an indexed, target-directed equality path (with explicit
authority) and must not invoke a full ambient-fact scan at every generated
term. Nothing in the observed callers currently justifies a general e-graph.

### Context-dependent order-endpoint keys

`order_endpoint_bucket_key` in
`src/kernel/assumptions/proposition_reasoning.rs` builds a theory-aware key for
context-inconsistency bucketing. It resolves memory loads, folds and sorts
addition, and recursively canonicalizes addends, but stops at
`ORDER_ENDPOINT_BUCKET_KEY_DEPTH = 6`. The result is useful as an index key,
yet it is neither the global assumption-free canonical form nor complete at a
fixed context.

This issue also owns that cutoff and terminology. The replacement may be a
complete input-sized normalization used only for bucketing, or a differently
structured index that does not require extracting a contextual representative.
It must preserve the existing near-linear consistent-context scaling property
and must not turn endpoint registration into all-pairs theory comparison.

## Why an e-graph is not automatically the answer

An e-graph or congruence-closure structure can represent proved ground
equalities without repeatedly rewriting syntax. Within one graph, an e-class
identifier can stand for a context-local equality class, and congruence links
can make equal parents share a class after equal children merge. That may be a
useful implementation of the equality-index layer.

It does not by itself define the canonical term required here:

- an e-class can contain many syntax trees, so extraction still needs a
  deterministic representative and cost function;
- equality saturation applies rewrite rules until saturation or a resource
  limit, reintroducing search/fuel if used without a finite exact rule set and
  a proof of termination;
- e-class identities are local to one evolving assumption context and can
  change across persistent proof branches, while canonical terms must remain
  stable across those contexts;
- merging a class because of an assumed proposition must preserve that
  proposition's proof provenance rather than turning it into definitional
  equality; and
- a mutable or fully cloned graph per persistent proof context would violate
  Click's relevant-input scaling requirements unless its ownership and
  persistence model were designed carefully.

Do not introduce a general saturating e-graph into the kernel as a replacement
for the three-round loop. An e-graph remains a possible indexed
representation for context-local proved equality, or a possible surface
planning tool that emits explicit rewrite evidence. That decision comes after
the semantic layers and caller requirements are separated.

## Intended architecture

1. **One operation owns canonical identity.** `canonical_term`,
   `canonical_offset_term`, and corresponding condition traversal implement
   only assumption-free representational normalization. Their contracts state
   and test determinism, idempotence, and completeness over supported finite
   structures.
2. **Proved equality remains contextual.** Equality indexes operate on
   already-canonical keys and return a class answer or an evidence path. They
   never mutate the canonical syntax of a term merely because a new premise is
   assumed.
3. **Vocabulary changes are explicit.** A producer that needs a range or
   pointer expressed through proved equalities requests a targeted contextual
   rewrite. Planning selects the equality path outside the authoritative
   kernel where selection is nontrivial; the kernel checks named edges and the
   local structural/congruence steps.
4. **Index normalization is named by purpose.** Order-endpoint bucketing may
   normalize associative addition or resolved loads, but it is not called the
   global canonical form unless it satisfies that form's exact contract.
   Bucket-key incompleteness may cost performance but must not change the
   logical inconsistency answer.

The implementation need not force all consumers to store large proof trees.
It does require an explicit answer to where rewrite authority lives and how a
recorded range remains related to its source expression. A compact typed path
or constructor-local equality certificate may suffice.

## Intended regressions

Before replacing the implementation, construct a focused regression that
requires more alternating simplification/equality layers than the current
three rounds. Demonstrate that applying the present contextual operation twice
can make further progress, or otherwise characterize precisely why the current
composition happens to be idempotent despite lacking such a proof. The
regression should exercise the actual memory-range or pointer caller rather
than only a private helper.

Then retain the following permanent coverage:

- canonicalizing the output of `canonical_term` again returns the exact same
  term for constants, arithmetic trees, conditionals, folds, nested pointer
  offsets, resolved loads, and unresolved loads;
- two terms differing only in representational memory history have the same
  canonical form at depths beyond the former 64-level preflight;
- adding an ordinary proved equality to a `PureFactContext` does not change the
  assumption-free canonical forms of either side;
- using that equality for a contextual range rewrite requires and retains the
  exact evidence, and tampering with an edge or term is rejected;
- same-load-count proved aliases are either handled by the equality index or
  by explicit rewriting, not by input-dependent "canonical" spelling;
- deep order endpoints are bucketed without a six-level logical cutoff, and a
  contradictory context is detected independently of endpoint nesting; and
- multi-size deterministic measurements show near-linear work in the relevant
  term, equality path, and emitted certificate. Adding unrelated facts does
  not change a direct canonicalization curve.

## Design decisions

Resolve these from caller evidence rather than by choosing a data structure
first:

- Can verified-call and resource footprints stay in their original canonical
  syntax while later matching uses an explicit equality path, or must they be
  rewritten at creation to remain stable after the equality leaves scope?
- If creation-time rewriting is required, which component chooses the target
  vocabulary and what compact evidence remains attached to the result?
- Is an exact ground-equality component index sufficient, or do the observed
  callers require congruence closure through rewritten subterms?
- Can order inconsistency use several cheap sound bucket keys and reserve
  pairwise theory checks for a narrowly identified bucket, avoiding any need
  for one context-dependent extracted representative?
- Should contextual equality classes use a persistent union/find-like index,
  a proof-producing e-graph in the surface planner, or the current adjacency
  index with targeted path queries? Any choice must account for branching,
  provenance, deterministic work, and deep structural keys.
- Which currently documented statements about "canonical at creation" refer
  to the assumption-free representation, and which accidentally promise
  context-dependent rewriting?

## Acceptance criteria

- The public internal contract for canonicalization explicitly requires
  idempotence, determinism, assumption independence, and complete traversal of
  supported finite input.
- `canonical_term(canonical_term(term)) == canonical_term(term)` is covered
  across every term family and multiple deep sizes.
- No proof result skips definitional canonical comparison because a term
  crossed an opaque numeric depth. `bitvector_term_deeper_than(..., 64)` is not
  used to decide whether canonicalization applies.
- Canonicalization performs no ambient fact lookup, equality-class selection,
  theorem application, condition decision, or proof search.
- Context-dependent transformations are renamed and separated from canonical
  identity. They use only exact named/indexed evidence, or are planned outside
  the kernel and checked from an explicit certificate.
- `CONTEXTUAL_LOWERING_ROUNDS` and the alternating fixed-round loop are deleted.
  They are not replaced by an unbounded `while changed` loop without a
  well-founded measure and relevant-input scaling proof.
- `ORDER_ENDPOINT_BUCKET_KEY_DEPTH` is deleted, and endpoint indexing remains
  logically complete and near-linear on consistent contexts.
- Equality justified by a premise retains provenance and never becomes
  assumption-free definitional equality.
- No complete fact-set scan, complete persistent-context clone, or deep-term
  structural cache key is introduced on a hot path without the scaling design
  and regressions required by
  `docs/internals/verification-efficiency.md`.
- Documentation uses "canonical form" only for the assumption-free operation
  and names contextual equality or rewriting explicitly.
- `click verify`, `click expand`, `click profile`, and `click audit` agree on
  every affected proof after the migration.

## Non-goals

- Treating all mathematically or propositionally equal expressions as one
  definitional term.
- Adding broad algebraic rewriting, SMT solving, or equality saturation to the
  kernel.
- Making canonical syntax depend on whichever facts happen to be in scope.
- Preserving compatibility for low-level internal APIs or misleading method
  names.
- Using a larger round/depth limit as the fix.

## Staged implementation and stopping points

Each stage should be a coherent green commit. If a later stage exposes a
larger representation migration, the earlier stage must remain truthful and
useful on its own.

1. **Lock down terminology and the real invariant (complete).** Broad
   idempotence and assumption-independence tests cover `canonical_term`.
   Private helpers whose behavior is contextual or key-specific are named as
   lowering and bucket-key operations, without changing semantics.
2. **Reproduce and inventory (complete).** Add the layered contextual-lowering
   reproduction, record every direct caller and required output property, and
   measure work across term depth, equality-path length, and unrelated facts.
   The layered case is closed by the inner generated-term worklist rather than
   the nominal round count; the exact boundary and remaining lack of a general
   idempotence proof are recorded above.
3. **Make true canonicalization complete and stack-safe.** Replace recursive
   deep-load traversal with an iterative implementation, delete the 64-level
   preflight, and land multi-size regressions. This stage is independent of
   how contextual equality is represented.
4. **Separate contextual footprint lowering.** Prefer target-directed explicit
   equality evidence. Preserve the verified-call and resource regressions that
   motivated creation-time lowering. Delete the three-round loop only once all
   callers use the replacement.
5. **Repair order-endpoint indexing.** Replace the depth-six key construction
   with complete, purpose-named normalization or a bucket strategy whose misses
   cannot affect the logical answer. Retain the consistent-context scaling
   regression.
6. **Evaluate an e-graph only if evidence remains.** If callers still require
   congruence closure, prototype it outside the kernel or as a proof-producing
   index and compare its deterministic scaling and persistent-branch costs
   with targeted equality paths. Do not make completion depend on this
   optional experiment.
7. Update `docs/internals/canonicalization.md`, the glossary, and any comments
   that conflate canonical identity with contextual equality, then run the full
   repository gate.
