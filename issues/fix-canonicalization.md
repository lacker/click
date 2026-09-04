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

### 3. Explicit contextual restatement

Some proofs need to view a value in vocabulary different from its canonical
syntax. The motivating case is a verified call's mutable memory footprint: the
list of `(base pointer, start, end, element width)` ranges that its contract
says the call may change. A contract may spell an endpoint as `new_len`, while
an entry-state equality relates it to `old_len + 1`, and another equality may
reduce `old_len` to a constant. A later frame or disjointness proof may be
written in either of those other vocabularies.

The footprint itself keeps its assumption-free canonical syntax. A proof that
needs another spelling explicitly derives an equivalent range or effect-summary
view using named equalities. This is the ordinary distinction between
definitional equality, which canonical comparison handles automatically, and
propositional equality, which requires a rewrite or transport step. A smart
tactic may plan and emit that step automatically, but the kernel only checks
the requested destination and its evidence. The alternate spelling does not
replace the stored footprint or become the canonical form of `new_len`.

## Current behavior

### Assumption-free canonicalization

`canonical_term` is a fixed composition of structural load canonicalization
and load-variable replacement. Existing tests cover a representative
idempotence case, and the documentation claims determinism and idempotence.
Proposition reasoning used to guard a deep structural comparison with
`bitvector_term_deeper_than(term, 64)`. Inspection found an important nuance:
in the current equality flow the preceding `decide` path already reaches the
memory-resolution equality graph, whose vertices are keyed by
`canonical_term`. The guarded comparison was therefore redundant for the
known callers rather than a reproduced proof result that changed at depth 65.
It was still an invalid and brittle boundary: a small control-flow refactor
could have made the fallback's opaque cutoff observable, and the recursive
preflight walked embedded memory as well as the explicit term.

Stage 3 removed that preflight and the two recursive implementations beneath
the true canonical form. Structural load canonicalization, load-variable
substitution (including every condition family and pointer offsets), and
top-level offset canonicalization now use explicit worklists. Chains in which
one materialized cell stores a load of the next cell are followed iteratively
as well. The whole-term memo tables are retained for ordinary shallow terms
because expansion performance depends on them, but an iterative structural
preflight makes deep terms bypass those caches: their derived `Hash`/`Eq`
operations would otherwise recursively walk the same structures before the
iterative body ran. This numeric threshold is only a cache policy and cannot
change a proof or canonical result. Narrow caches for memory-DAG and load
identities remain unchanged.

Multi-size regressions exercise conditional terms at depths 1, 8, 32, 96,
and 256. The two canonicalization passes visit respectively
`8/49/193/577/1537` and `7/49/193/577/1537` term nodes, within a linear bound,
and a second application returns the exact same term. A separate resolved-load
regression at depths 64, 128, 256, and 512 visits each explicit node once and
reaches the deepest cell. Pointer-offset canonicalization is independently
covered at depths 64, 128, and 256. Two depth-128 terms whose only difference
is irrelevant snapshot history also have identical canonical forms and prove
equal through the public proposition path.

### Former context-dependent footprint lowering (removed in stage 4)

`PureFactContext::lower_bitvector_under_assumptions` in
`src/kernel/assumptions.rs` was added as a prototype for lowering memory
footprints at creation. Before stage 4 it ran three alternating rounds:

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

The production uses were narrow, but the original inventory missed a third:

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
- atomic proposition derivation used
  `lower_bitvector_via_recorded_equalities` directly to choose substitutions
  that made a larger arithmetic proposition normalize. This was the same
  representative-selection policy hiding behind another kernel proof path.

Stage 4 removed all of these helpers and the characterization-only counters.
Arithmetic and load-address goals now close through target-directed equality
paths and explicit surface rewrites; verified calls never invoke contextual
lowering while creating their footprint.

`simplify_bitvector_under_assumptions` has many other callers. This issue does
not assume that the general simplifier can simply be deleted; it requires that
canonical identity and contextual footprint lowering stop depending on its
search-capable behavior.

### Stage 4 boundary decision

The replacement does not choose a preferred contextual representative when a
verified call is created. The evaluated mutable footprint is put into
assumption-free canonical form and remains the call-memory derivation's and
`CMemoryEffectSummary`'s authoritative stored footprint. This gives the call
one stable representation independent of the entry facts that happened to be
available.

When a later proof needs, for example, `data[0..old_len + 1]` while the stored
summary says `data[0..new_len]`, it requests an equivalent view for that proof.
The request names the source range, destination range, and exact evidence for
any changed base offset, start, and end. The checker preserves the pointer
block and element width, checks each equality or constructor-congruence step,
and derives the alternate view without mutating the original summary. Different
proofs may therefore use different convenient spellings without changing term
or footprint identity.

The smart layer is expected to perform the routine automation: notice a range
vocabulary mismatch, find a short path in the indexed ground-equality graph,
and emit the explicit restatement. `click expand` must expose that operation,
and the same operation must be writable directly in the low-level proof form.
Repeated uses may reuse a previously derived view or a planner cache; that is
not a reason for the kernel to select and store a speculative representative.

Load-variable congruence follows the same boundary but is a separate checked
operation. Given the load variable for `load(memory_epoch, data[i])` and an
explicit proof that `i == 0`, an address-congruence step may derive equality
with the load variable for `load(memory_epoch, data[0])`. It preserves the
memory epoch and pointer block and checks the offset equality. It does not call
general contextual term lowering to manufacture another equality-graph node.

The checked rewrite language is deliberately small:

- exact named equality premises, with symmetry and transitivity;
- congruence under the term and pointer-offset constructors traversed by the
  certificate; and
- deterministic, local constructor reduction such as constant addition.

It does not include general condition proving, theorem search, fold reasoning,
ambient fact scans, or equality-class representative selection. If a smart
tactic uses richer reasoning to find a rewrite, it must compile that reasoning
to the ordinary explicit proof steps the kernel already checks.

The implementation uses the existing proof-object vocabulary rather than a
second effect-summary proposition. A `frame using` operation is the typed
consumer of a proof-local range view: its target is the selected function
effect, its source ranges remain the canonical `CMemoryEffectSummary` ranges,
and its listed equality/bound premises are checked as retained
`PropositionDerivation`s. Smart `frame()` selects those premises and leading
`have` steps; expansion prints the same `frame() using { ... }` operation that
can be written directly. The stored summary and the call-havoc derivation are
not mutated or duplicated.

Load-address congruence has its own retained atomic evidence. It checks two
registered load variables against their exact origins, requires one memory
epoch and pointer block, and recursively checks structural offset congruence
plus exact ground-equality paths. Smart expansion turns those paths into
ordinary `rewrite` operations followed by `normalize`; the equality graph no
longer manufactures a contextual load-variable neighbor.

### Stage 2 deterministic-work characterization

Before stage 4 removed the implementation, test-only counters measured actual
contextual simplifier calls, full-fact visits made by direct constant-equality
lookup, equality-worklist vertices, and outer rounds. The regression used raw
terms so eager constructors could not erase the intended shape. The recorded
results were deterministic:

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
3. **Canonical footprints are the stored default.** A verified call stores its
   evaluated mutable ranges in assumption-free canonical syntax in both the
   memory derivation and `CMemoryEffectSummary`. Entry assumptions never choose
   a replacement spelling for that stored identity.
4. **Vocabulary changes are explicit derived views.** A particular frame,
   disjointness, or load-address proof may restate a canonical range or pointer
   through exact proved equalities. Planning selects the destination and path
   outside the authoritative kernel; the kernel checks the named edges and
   local structural/congruence steps and retains the original representation.
5. **Index normalization is named by purpose.** Order-endpoint bucketing may
   normalize associative addition or resolved loads, but it is not called the
   global canonical form unless it satisfies that form's exact contract.
   Bucket-key incompleteness may cost performance but must not change the
   logical inconsistency answer.

The implementation need not attach a large proof tree to every future range
query. The checked proof event must retain how its derived view follows from
the stored source. A compact typed path or constructor-local equality
certificate may suffice, and an already-derived view may be reused.

## Intended regressions

Stage 2 constructed a focused case with more alternating
simplification/equality layers than the nominal three rounds. It established
that the inner generated-term worklist closes that case in one phase, while
also exposing the cubic direct-fact scan and the absence of a useful contract
for the general operation. The permanent replacement coverage is:

- canonicalizing the output of `canonical_term` again returns the exact same
  term for constants, arithmetic trees, conditionals, folds, nested pointer
  offsets, resolved loads, and unresolved loads;
- two terms differing only in representational memory history have the same
  canonical form at depths beyond the former 64-level preflight;
- adding an ordinary proved equality to a `PureFactContext` does not change the
  assumption-free canonical forms of either side;
- a verified call stores the same canonical source footprint in its call-havoc
  derivation and `CMemoryEffectSummary`, regardless of unrelated entry facts;
- restating that footprint for a particular proof requires and retains the
  exact endpoint evidence, leaves the stored footprint unchanged, and rejects
  a changed block, element width, edge, source, or destination;
- smart expansion automatically emits the restatement needed by the motivating
  verified-call/frame proof, while an equivalent explicit proof checks without
  invoking contextual search;
- load-variable congruence across proved-equal offsets uses its narrow checked
  address step and rejects a changed memory epoch or pointer block;
- same-load-count proved aliases are either handled by the equality index or
  by explicit rewriting, not by input-dependent "canonical" spelling;
- deep order endpoints are bucketed without a six-level logical cutoff, and a
  contradictory context is detected independently of endpoint nesting; and
- multi-size deterministic measurements show near-linear work in the relevant
  term, equality path, and emitted certificate. Adding unrelated facts does
  not change a direct canonicalization curve.

## Resolved and remaining design decisions

Stage 4 has resolved the semantic choices:

- Verified-call footprints remain in their original assumption-free canonical
  syntax; a contextual spelling is an equivalent derived view, not replacement
  identity.
- The smart planner chooses a destination when automation is requested. The
  kernel never chooses a “best” member of an equality class.
- The expanded or directly written proof names the destination and exact
  endpoint/address evidence. The kernel checks that evidence locally.
- Footprint restatement and load-address congruence are distinct operations;
  neither is implemented by a general contextual-lowering helper.

Stage 4 resolved its representation questions:

- A footprint restatement is consumed directly by the exact `frame using`
  operation; it does not derive a second `CMemoryEffectSummary`.
- Existing equality propositions, retained `PropositionDerivation`s, and
  leading `have` steps cover range bases and bounds. There is no parallel
  endpoint proof language.
- The restatement lives in the function-effect proof, where expansion already
  prints `frame using` and its exact premises. The verified-call statement
  event continues to record only the canonical source summary.
- Exact ground-equality paths plus target-directed structural congruence cover
  the observed cases. The former generated-term representative walk is gone.

The remaining choices belong to stage 5 or the optional later experiment:
- Can order inconsistency use several cheap sound bucket keys and reserve
  pairwise theory checks for a narrowly identified bucket, avoiding any need
  for one context-dependent extracted representative?
- Should the smart planner use the current adjacency index with targeted path
  queries, or does evidence eventually justify a proof-producing e-graph?
  Stage 4 starts with targeted paths; any alternative must preserve branching,
  provenance, deterministic work, and deep structural-key constraints.
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
  identity. A stored call footprint stays canonical; alternate range and load
  views are planned outside the kernel and checked from explicit evidence.
- The kernel does not automatically choose a footprint vocabulary from ambient
  assumptions. Smart automation emits the same explicit restatement available
  to a directly written proof, and expansion displays it.
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
3. **Make true canonicalization complete and stack-safe (complete).** The
   structural and load-substitution passes, including condition operands and
   pointer offsets, now use explicit worklists; materialized root-load chains
   are iterative; deep inputs bypass recursive whole-term memo keys; and the
   64-level logical preflight is gone. Multi-size idempotence and linear-work
   regressions cover depths beyond the former cutoff. The cutoff turned out to
   be redundant in the current equality flow, not a known observable proof
   failure; removing it still closes a brittle logical boundary.
4. **Replace contextual lowering with explicit restatement (complete).** The
   evaluated canonical footprint remains unchanged in call memory and
   `CMemoryEffectSummary`; exact `frame using` consumes proof-local range views
   from named equality/bound premises, and smart frame planning emits that
   operation automatically. Load-variable equality uses retained,
   target-directed address-congruence evidence and expands to exact rewrites.
   The heuristic representative walk, its generated-term arithmetic use,
   `load_variable_congruence_neighbor`, and `CONTEXTUAL_LOWERING_ROUNDS` are
   deleted. Regressions cover the verified-call vocabulary mismatch,
   independently checked expansion, and rejection across different load
   epochs and blocks.
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
