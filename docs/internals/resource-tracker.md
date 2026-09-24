# The resource tracker

The resource tracker is the one place in the kernel that knows **which
resources are known to be the same at which program points**. It is an
internal Rust interface. It adds no Surface Click syntax, no tactic and no CLI
command, and it does not change which C programs Click accepts.

It exists because that question was already being asked in several places,
each with its own walk and its own answer, and because the answer a walk threw
away — *where* it stopped and *why* — is exactly what a user needs when a
proof fails with two terms that spell alike.

## The vocabulary

- **resource** — a piece of mutable state, or part of one. Today: a memory
  cell, a memory block as a pure function reads it through an array argument,
  one model field of a resource instance, and one counted population. A byte
  range, a struct extent and a local are the kinds that come next.
- **program point** — a point on the current proof path (`entry`, a `mark`ed
  label, "here"), identified by the memory snapshot the kernel had reached
  there, or — for the two kinds whose version is a value rather than a point —
  by the whole saved state.
- **same** — the two points are known to hold one version of the resource.
- **changed** — a step between them wrote the resource.

"Unknown" is the third answer and the interesting one: a step between the two
points could not be *shown* to leave the resource alone. The resource may well
be unchanged; nothing states it. A missing fact and a real write are different
failures and get different words.

## The interface

`src/kernel/resource_tracker/mod.rs`:

```rust
last_same(resource, at: &ProgramPoint) -> Option<LastSame>   // { point, stopped_by: Stop }
same(resource, left: &ProgramPoint, right: &ProgramPoint) -> Sameness
explain(resource, here, there) -> Explanation
explain_last_same(resource, here) -> Explanation
last_same_point(resource, at) -> Option<ProgramPoint>        // the naming path
```

`Sameness` is `Same`, `Changed { at, by }` or `Unknown { at, why }`. `Stop`
pairs a `Change` — what happened at the point the walk stopped at: a store to
an address, a call's havoc with its write set, a loop's havoc, a free, an
allocation, a declaration, a lifetime end, cells forgotten, the beginning of
the history — with a `StopReason`: the step `Affected` the resource, or it was
`NotShownSeparate` and by which `SeparationCheck`, or the history ends there.

`Resource` is borrowed, so asking costs the same as the walks cost before.
`Explanation` is bounded: the resource, the answer, and how many recorded steps
the tracker crossed after the blocking one. It never carries memory.

## Two kinds of point, because there are two kinds of version

A memory resource's version **is** a point: the snapshot the cell was last
written at. That is what makes `last_same_point` a naming path — a load
variable's name can embed the point, and equal names then mean equal terms.

A model field's version is the **value stored in the instance**, and a counted
population's is the `count` term the state holds. Neither is a point on the
memory history: a `fold` changes resources and not memory, and a call that
returns ownership keeps the instance's identity while replacing its field
vector. So their points are whole saved states — `StatePoint`, a *handle* to a
state the kernel already keeps (`entry`, a `mark` out of `RecordedSnapshots`, a
loop's iteration state, the live one), never a copy.

```rust
same_at_states(resource, left: StatePoint, right: StatePoint) -> Sameness
explain_at_states(resource, here, there) -> Explanation
sole_population_of_family(state, family) -> Option<OwnedResource>
```

Three decisions are worth writing down.

- **A field's version is its stored value**, with no generation counter and no
  new per-instance state. An instance that survives a call keeps its identity
  and gets fresh field variables, so the stored value already distinguishes the
  versions. Adding a counter would be a second answer to a question the state
  already answers.
- **It answers `Unknown`, never `Changed`.** `Changed` is what a recorded write
  earns, and no `CMemoryDerivation` edge carries "field *k* of this instance was
  replaced". The *step* is still named, but it is read from the mint rather than
  from a walk — see below.
- **It fails closed.** `Same` needs both lookups to succeed and the two values
  to be syntactically equal. A missing instance, a missing population, a
  parent-qualified path this lookup does not resolve, and two different
  spellings of one value all answer `Unknown`. A tracker that answered `Same`
  for a field a contract did not promise would verify a false theorem.

`last_same` and `last_same_point` return `None` for both kinds, exactly as they
do for `Ranges` and `AnyMemory`: no term is named by one of these points, so
there is no oldest point to be. `step_effect::affects` is never asked about
them, because a memory edge is not between them.

### Where the step comes from

The mint. `src/kernel/model_fields.rs` registers every fresh model-field
variable where it is minted, with the instance it belongs to, which field of the
schema it is, and **why** it was minted — a call returning ownership, a
`produces`, a loop head, contract/implementation refinement, or the contract's
own entry model. The mint site is the only place that knows why.

`same_at_states` reads the step off the two values it already fetched: a value
the contract's entry minted is the *old* version, so the other side's mint is
the replacement. Where neither side was minted as an arbitrary model, nothing is
claimed and the text says only what it can see.

The same registry is what lets a refusal spell `v1000002` as `c.rank`, and the
entry model as `old(c.rank)`, in the one place terms are spelled
(`describe_bitvector_with_context` and `proof_diagnostics::render`). The
instance's own name comes from the surface, which registers it where it resolves
a field access and where a verified function declares its binders; a name only
half known prints nothing, because a half-spelled field would look like source
the reader could search for.

The registry is diagnostics only — no rule, no premise and no name a term
carries reads it — bounded like the other memos, and emptied when a
`VerificationSession` starts, beside the load-variable registry.

### The efficiency contract

A question is **one keyed lookup in each state's resource context, plus one term
comparison at the single key asked about**. Nothing enumerates a resource
context, nothing compares two states (two points are one point by handle
identity), nothing walks a change history, and nothing is memoized — the answer
reads path state, which may not be cached by content across verifications.

Like the memory cases, it runs **only while building a refusal**. There is no
per-step history of resource-context changes and no walk of
`ResourceContextChange` at query time.

`version_at_state` records one deterministic work unit per lookup, so the claim
is measured:
`a_saved_state_version_costs_one_lookup_per_point`
(`src/kernel/resource_tracker/tests.rs`) grows both states by unrelated
instances and unrelated populations over 8, 16, 32 and 64 and asserts two units
at every size, with the answer checked each time. Deterministic work for a
passing proof is unchanged to the unit: the named-operation totals of
`augment_rotate_callback_child_read`,
`contract_owns_composite_argument_across_forms` and
`rb_replace_node_with_children` are identical with and without this chunk.

`sole_population_of_family` is the one place that walks a state's population
list, and it walks it to turn the family the reader wrote into the key the state
indexes by. That list holds one entry per family the contract's clauses brought
into scope, so it is sized by the selected source; where a family has two live
instantiations it answers nothing rather than the wrong one.

`last_same_point` is the only form on the hot path. It is what a term that
reads memory is named by: a load variable embeds the oldest point its cell is
the same as, and an array argument carries the oldest snapshot that still
agrees about its block, so equal names mean equal terms. The stop information
is *computed from the point the walk stopped at* rather than recorded along the
way, which is why naming pays nothing for it.

## What it is not

- It has **no ownership rules**. It never decides who may read or write a
  resource. It has no overlap logic of its own: it asks the resource and
  assumption layers whether two footprints are separate.
- It **never looks inside a proposition**. A term matters to it only through
  the resources the term reads; a fact only through its terms.
- It **does not search**. Every question is a bounded walk over recorded
  history with exact lookups, so it gives the same answer wherever it is asked.

## The soundness corridor

The tracker reads `CMemoryDerivation` edges (`docs/internals/memory-dag.md`).
Interning is first-wins, so one edge can be shared by proof paths with
different assumptions. An edge may therefore carry only what is true on
*every* path that could produce that snapshot: a write set qualifies, a
path-dependent separation does not. The two naming walks are consequently
assumption-free — an answer that is embedded in a name and memoized per
interned snapshot must not depend on one path's facts — and the evidence for
crossing an edge is re-derived in the querying context instead of being stored.

The mirror rule holds on the query side: retained evidence names premises,
never a context (`docs/internals/proof-objects.md`).

The two version memos (per `(snapshot, pointer)` and per `(snapshot, block)`)
are cleared with the other canonical-form caches when a `VerificationSession`
starts, because interning dedups by content and one verification's history
must not answer the next one's question.

## One rule, and its answers

There is one decider, `resource_tracker::step_effect::affects`, and every walk
calls it: "does this recorded step affect this resource?", answered `Affected`,
`Separate(how)` or `NotShownSeparate(check)`. A step kind is therefore answered
once, and a new one has to be answered for every resource before it compiles.
`Separate` carries what justified it — a checkable hop for a cell, a structural
claim about objects for a block, the step's own write set missing every range
for a footprint — so `explain` and retained evidence say only what was actually
established.

| Recorded step | A cell | A block, as an array argument | A stated footprint |
| --- | --- | --- | --- |
| `Store` | separate on proven-distinct blocks, a common-base offset inequality, typed `separate(..)` evidence, an explicit range, general distinctness, or two owned members of one composition | separate **only** on `PointerBlock::proven_distinct` | separate when the written bytes miss every range |
| `BlockDeclared` | separate under the extended-bridging gate: it writes nothing | separate when the declared object is proven distinct: it has its own `blocks` key, so this block's extent is the entry it was | separate: it writes nothing |
| `HeapAllocationPending` | separate under the extended-bridging gate | separate: a request with no address yet records nothing a read of a block consults | separate: it writes nothing |
| `ContractAllocationClaimsChanged` | separate under the extended-bridging gate | **stops** | separate: it writes nothing |
| `ContractAllocationRetired` | separate when the possibly released allocation misses the cell, or, on every path including naming, when the retiring call's own havoc covers the whole allocation | separate when the allocation's object is proven distinct | separate when its bytes miss every range |
| `CellsForgotten` | separate under the extended-bridging gate | **stops**: the state is the same, the cell map is not | separate: it writes nothing |
| `HeapAllocated` | separate under the extended-bridging gate when the block differs | separate when the fresh object is proven distinct | separate: a stated footprint names objects that already existed, so the fresh one's bytes are in no range of it |
| `LocalLifetimeEnded` | separate under the extended-bridging gate, on general distinctness | separate when the retired object is proven distinct | separate when the retired object is proven distinct from the object every range is in |
| `HeapFreed` | separate on two separation ladders, both inside the extended-bridging gate | separate when the released allocation's object is proven distinct | separate when the released bytes miss every range |
| `CallHavoc` | separate on range disjointness | separate when every declared range's object is proven distinct | separate when every declared range misses every range |
| `LoopHavoc(Some)` | separate under the extended-bridging and explicit-check gates, and never on the naming path | separate when every declared range's object is proven distinct | separate when every declared range misses every range |
| `LoopHavoc(None)` | never separate | never separate | never separate |

Two kinds still refuse a block outright, and both for want of a name on the
edge: `ContractAllocationClaimsChanged` names no allocation, and a contract
claim may cover a subrange of `ExternalArgument` memory; `CellsForgotten` names
no cell, so nothing says the values it dropped were not this block's. Recording
what they concern is what would settle either.


A contract with undecided allocation continuity records
`ContractAllocationRetired` for the consumed input. It removes cached cells,
initialization, and zeroed status under equal pointer spellings, while leaving
definite deallocation unasserted. The edge names the allocation and its extent,
so a later memory proof may cross it only for storage shown separate from that
possible release.

The call rule reads the consumed resources, and so the retired allocation, at
the call's entry: the post-call value of a pointer field the callee owned is a
fresh load, and a callee that frees `box->data` and re-points it at memory the
caller keeps would make a post-call reading retire the wrong object. A kept
owned memory fact then needs no written separation from the retired
allocation when one owned memory fact the caller lent covers the allocation's
whole byte range: the two were held at once, and owned memory is exclusive
within one valid composition. A kept view, a kept composite, or any kept fact
when no lent owner covers the allocation still needs a separation the path
facts prove (`caller_resource_left_stale_by_retirement` in
`src/kernel/functions.rs`).

Reading at entry makes every consume/produce of an allocation-bearing
composite whose continuity the contract leaves open record a retirement right
after the call's `CallHavoc`, followed by the returned claim. When one of that
havoc's ranges covers the retired allocation by structure (the range starts at
the allocation's base and spans at least its byte count), the retirement is
transparent to cell values (`retirement_inside_its_call_havoc` in
`src/kernel/resource_tracker/cell_source.rs`, hop
`RetirementInsideItsCallHavoc`). It writes no byte, and the only reason a
retirement stops a cell is that a later owner may reuse released addresses, so
a load after it must not be named by a value from before the call. No byte of
this allocation can reach one: every such byte lies in a range of the havoc
just below, and a walk crosses a havoc only on a proof that the cell misses
every range, so it stops at the havoc and names the call's post-call value. The
retirement keeps that havoc's forget mark for the same reason
(`retirement_keeps_its_call_havocs_forget_mark`), so the content-addressed
projections load naming interns agree with the walk. Without this, the
produced composite's fields were named at the havoc (where the return
resources are evaluated) and later reads at the retirement, and every further
reallocating call added one nested heap-extent proof to relate the two.

Where the cell column names a gate, the answer is one a scope decides rather
than the edge. `extended_dag_bridging_active` and `explicit_dag_check_active`
(`src/kernel/memory_provenance.rs`) are scoped flags, set for the duration of
the memory-load prover and of explicit certificate validation and cleared
outside them. The wider answers are confined to those scopes because the
narrower ones are what execution pruning, load canonicalization and `simp`
planning check a certified form against, and a rule that widened everywhere at
once would make generation and check of the same query disagree. So the gate
belongs on the row: outside the scope the cell arm is the pre-arc walk, which
crosses no declaration, no forgotten-cell edge and no free, and inside it the
rows above hold. The two arms that then still answer `Affected` say so either
way — a free of this very allocation is a change, gate or no gate — because a
scope may withdraw a claim of separation and may not withdraw a recorded write.

The `Store` row is the one that is gated rung by rung rather than whole.
Proven-distinct blocks, the common-base offset inequality and the owned
composition are spent in every scope; the typed `separate(..)` evidence and the
explicit range are spent under the explicit-check gate, and general
distinctness under the extended-bridging one. Two of those rungs also stand or
fall with the byte question — `access_byte_overlap` below — because they prove
two addresses differ and a gap narrower than the wider access is no separation
at all.

The third column is `footprint_effect`, the arm `Resource::Ranges` and
`Resource::AnyMemory` reach. A footprint is a list of byte ranges a resource
fact was derived from, and the answer is spent *dropping* that fact, never
naming a term and never retained as a premise. That is why it may be coarser
than the cell arm and is: a write through a block that may be any object
(`memory_block_may_alias`) affects every footprint outright, rather than being
asked whether that block is proven distinct from each range. It is also why the
arm is handed no fact context — for the opposite reason to the block arm's,
which is that removing a resource fact more often is always sound, while
naming a term with an answer one path's facts decided is not. `AnyMemory` is
the footprint the kernel could not name: nothing bounds what it covers, so only
the kinds that write no byte are separate from it, and every other kind stops.

The difference that stays is *what evidence a resource may spend*: a block may
use only the kernel's structural separation, because its answer is embedded in a
name that is shared across proof paths, and the rule enforces that by handing
the block arm no fact context at all. Where the cell column reads a stated
`separate(..)`, an offset inequality or a resource composition, the block column
reads only `PointerBlock::proven_distinct` and the checked write set the edge
itself carries — which is path-independent, and so may be read off an interned
edge.

Two of those answers are not reachable from C0 yet, and fail closed where they
stop: a `free` of an object distinct from the subject needs a `malloc`, whose
`branch` continuation is reached by a transition that records no edge, and a
loop's checked write set is separated from its own head state by a memory the
loop rule assembles map by map, also without an edge. Both are gaps in what the
execution records, not in the rule, and
`src/kernel/resource_tracker/tests.rs` pins the rule's answers directly.

One consequence a user meets today: a stated `separate(..)` carries a cell fact
across a call and does not carry an array fact, because the block walk has no
fact context to read it from. That one is not a difference to settle but the
corridor itself — a block's answer is shared across paths — so the refusal for
a whole-array fact says what is missing instead of naming a repair the walk
would never consult.

The cell walk is also asked a second question by memory-load reasoning — "are
these two loads equal" — and that caller keeps the whole path as retained
evidence. Both questions read the same edges under the same rules, which is
why the walk lives in `src/kernel/resource_tracker/cell_source.rs`.

## What the user sees

One renderer turns an `Explanation` into text, and every refusal whose real
cause is "two same-looking terms read different versions" uses it, so the
wording is identical everywhere:
`crate::surface::diagnostics::describe_resource_version_mismatch`.

It spells the resource with the user's own names (`a[m]`, `g[0]`), names the
one step that broke the chain, and prints, in short sentences, the repair for
the case that actually applies:

| Case | What it says |
| --- | --- |
| one array, two indexes | ``the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`.`` |
| one array, a store wider than its element | ``the store to `a[j]` writes 8 bytes where `a` has 4-byte elements, so it covers the 2 elements from `a[j]` up and `i != j` rules out only the first of them. State `i < j`, which puts `a[i]` below every byte the store writes.`` The disequality above is not the repair here, and the *order* is: `one_element_gap_separates_bytes` gets a one-element gap from an address ladder, a bare disequality leaves the direction open so both accesses must fit in it, and a strict order fixes the direction so only the lower access must. Where neither access fits in an element there is no such order and none is offered. |
| two objects nothing separates | ``the store to `g[0]` may have written it, because `a` may point into `g`. If they are separate, require `separate(memory(a[0..1]), memory(g[0..1]))`; where the contract already transfers `g[0..1]` with `owns` or `consumes`, declaring `views a[0..1]` says the same.`` |
| a call or a loop with a write set | ``the call in between may write `g[0..1]` …`` then the same two clauses |
| the resource was written | ``the store to `a[i]` wrote it.`` |
| the read has no source spelling | ``the store to `g[0]` may have written it, and nothing tells that address apart from this read.`` |
| a fact about a block | ``a fact about `a` as a whole does not carry across the store to `b[j]`.`` plus the note below |
| a model field across a call | ``` `c.rank` may have changed since function entry: the call to `bump` returned ownership of `c` with a new model, and `bump` promises nothing about this field. If it keeps the field, state `ensures c.rank == old(c.rank)` on `bump`.``` |
| a model field across a loop | ``` … the loop owns `c`, and a loop head is an arbitrary visit, so it gives `c` a fresh model. If the body keeps the field, carry it through as `invariant c.rank == old(c.rank);`.``` |
| a model field the state no longer holds | ``` `c.rank` names no model here: `c` was consumed since function entry, so this state holds no field to read. Name the value it had there, `old(c.rank)`.``` |
| a counted population | ``` `count(object_ref(obj))` changed since function entry: a `produces` or `consumes` transition in between moved it. The transition relates the two counts, so state that relation, as `ensures count(object_ref(obj)) == old(count(object_ref(obj))) + 1`.``` |

Every clause it proposes is one that verifies the situation it is printed for;
where none does, it says what is missing instead of naming a repair that would
not work. A whole-array fact is the case with no repair to name: the block walk
reads no stated separation at all, so the text says so rather than sending the
reader to write a `separate(..)` the walk will never consult. A model field
neither point holds is the other: `old(c.rank)` would name nothing either, so
the text says that rather than printing it.

The four model-field and population rows are pinned as refusals with their
verified repairs beside them:
`mdtests/model_field_across_a_call_that_promises_nothing.md` /
`model_field_kept_by_a_call.md`,
`model_field_across_a_loop_without_an_invariant.md` /
`model_field_kept_by_a_loop.md`,
`fold_field_names_a_consumed_model.md` / `fold_field_names_the_entry_model.md`,
and `population_count_across_a_produces_transition.md` /
`population_count_states_its_transition.md`.

The two cases that can spell both ranges offer two clauses, because two say the
same thing: a stated `separate(..)`, and — since a contract's transferred and
borrowed clauses denote disjoint memory, below — a `views` clause over the read.
The second names its condition ("where the contract already transfers
`g[0..1]`") rather than asserting it: this renderer is handed two addresses, not
the contract's clause list, and a range transferred only inside a folded
composite is not one the entry partition reaches.  Both clauses are ones the
reader can write, because `SourceCell::element_range` spells only a parameter or
a file-scope declaration and yields nothing for a local.

An index only the lowering has a name for is printed `a[…]`, never as the
kernel variable, and no inequality is proposed over a name nobody wrote. It
never prints memory, and it reports at most the blocking step plus a count of
the steps after it.

A read through a pointer the function received rather than an object it names —
a pointer a call returned, a pointer a branch join selected — has no source
spelling at all, so only one side of the comparison can be printed. The text
still names the store, because that is the step the reader has to be told
apart from their read, and it does not offer a `separate(..)` it could not
spell.

No recorded step carries a source span or statement text today, so a step is
described by kind and target ("a store to `g[0]`", "the call", "the loop"). A
line number would mean adding a source location to the `CMemoryDerivation`
edges at their producers in `src/kernel/primitives/memory_state.rs`; the edge
may carry it, since a span is path-independent.

## Every site that decides whether a change matters

This is the map of the kernel outside `src/kernel/resource_tracker/`. It exists
so that the next reader does not have to rediscover which of these sites are
copies of the tracker's rule and which are different questions wearing similar
predicates. It names functions and no commit, as the rest of
`docs/internals/` does: a commit pin records that the page was true once, which
is the one claim a reader cannot check against the tree in front of them, while
a function name is something `grep` either finds or does not.

The four classes:

- **routed** — the same question as `affects`, and it now calls it;
- **separation** — a resource-versus-resource separation predicate. These are
  not copies: each is one function, and `affects` itself calls them. Leaving
  one in place is the point;
- **another question** — not a staleness decision at all;
- **disagrees** — the same shape of question, but a rule that would answer
  differently. Routing it would change which programs verify, so it stays, and
  the difference is written down here instead.

### Step versus resource: the question `affects` answers

| Site | Class | Note |
| --- | --- | --- |
| `ResourceContext::invalidate_memory_support` → `memory_derivation_affects_footprint` `src/kernel/primitives/resource_algebra.rs` | **routed** | Walks the edges between two snapshots and drops every resource projection a step could have written. It now asks `affects` about `Resource::Ranges` for a stated footprint and `Resource::AnyMemory` for one the kernel could not name, and keeps the projection only where the answer is `Separate(Footprint(..))` — so this site is where `footprint_effect` is spent, and the only place it is. |
| `ResourceContext::entries_affected_by_memory_derivation` | another question | Chooses *candidates* from the interval index; the rule then decides. Its one obligation is to stay a superset of the steps `affects` does not answer `Separate` for — narrowing it would silently keep a stale projection. |
| `statement_call_havoc_views` `src/kernel/proof/execution.rs` | another question | Collects the call nodes between two states; asks nothing about a resource. |
| `matching_recomputed_call_havoc_views`, `c_memories_definitionally_equal` `src/kernel/api/contract_certification/contract_claims.rs` | another question | Matches two derivation chains edge for edge, to certify a recomputation. A whole-state equality, not a footprint. The second skips the `local:` blocks its kernel twin skips, and by the same one filter — below. The chain walk is where the two part: `transparent_base` descends past an edge that recomputation would not have minted — a store or a declaration whose block is spelled `local:`, a store whose value is the base's own load at that very pointer (a tactic materializing a symbolic load, which independent certification never does), and the two edges that name nothing, `ContractAllocationClaimsChanged` and `CellsForgotten`. That is a structural skip over *edges*, decided by spelling and by interned identity, and it is not the pointerless filter the twin spends; a `local:` name is what it reads, so an addressed local's store is stepped past here as well. Nothing is claimed about a version by descending, because the pair the descent reaches is still compared in full. |

### The eager half: a step applying its own write set

These run *at* the step, over every cell, in the producing context, before the
edge exists. Each decides the same abstract question as the matching arm of
`affects` and each decides it differently, so none is routed.

| Site | Class | Why it differs |
| --- | --- | --- |
| `call_havoc_keeps_cell` `src/kernel/primitives/memory_state.rs` | disagrees | For ordinary cells, keeps a cell only when plain `ranges_proven_disjoint_from_pointer` proves the declared write set cannot reach it. A local cell whose block has a differently spelled write-range base is retained only when the pointer-equality graph does not resolve that base to the cell; this catches assumed aliases while preserving direct same-block construction transitions. The rule's `CallHavoc` arm uses typed range evidence and the `_for_frame` expansion, which looks through composite definitions, so the two remain weaker in different cases. |
| `CMemory::with_call_memory_havoc`, `CMemory::matches_call_memory_havoc_result` | disagrees | The producer that applies a call's write set and the checker that re-derives what it would have written. Both now ask `call_havoc_keeps_cell`, so the retain rule is one function: the checker has to stay identical to the producer, not to the rule, and sharing the function is what makes that structural instead of remembered. |
| `loan_preserving_havoc_keeps_cell` | disagrees | Preserved-block membership **or** bytes `LoanLedger::permits_memory_access` refuses a write through. An ownership question, with fail-open polarity, and no pointer-alias reasoning at all — a loop body or a joined branch arm may write through any pointer it can reach, so separation has nothing to decide. The width it asks the ledger about is the wider of the cell's value and the widest typed overlay recorded there (`union_overlay_widths`), and an unknown width fails closed. |
| `CMemory::with_loop_memory_havoc_preserving_loans`, `CMemory::with_interface_memory_havoc_preserving_loans` | disagrees | The loop head and the interface join, which both ask `loan_preserving_havoc_keeps_cell`. Neither records an edge, so no rule covers either; what used to be the same retain written twice is now one function asked twice. |
| `CMemory::forget_zeroed_allocations_written_by` | disagrees | The other half of a call's write set: it drops the zeroed reading of every allocation the declared ranges may reach, because "reads as zero where unwritten" is a claim about contents that an unseen write invalidates exactly as it invalidates a stored cell. It drops the status for the whole allocation rather than narrowing it to a prefix, since a write set bounds where a callee may store and not where it did. The rule has no arm for it: a zeroed reading is not a resource the tracker names. |
| `CMemory::without_possible_aliasing_cells` | disagrees | A store's own eager drop, and the one site on this list that shares the rule's byte question: the address ladder is conjoined with `access_byte_overlap`, exactly as the rule's `Store` arm conjoins it, so a ladder that proves two addresses differ may stand in for byte separation only where the gap it establishes clears both accesses. Ahead of the ladder, and before `access_byte_overlap`, it asks ownership through the composition base index (`PureFactContext::access_owned_apart_from_store`, below); a cell ownership does not place goes down the ladder unchanged. The ladder itself is `pointers_proven_distinct_for_memory_resolution`, **or** `pointers_proven_disjoint_by_explicit_range_for_memory_resolution`, **or** `pointers_directly_disjoint_by_range`, **or** `owned_composition_store_separated_evidence`. The two range rungs are the cross-base pairs offset reasoning cannot decide and the byte question answers `Unknown` for; they are a range-index scan the rule's hot `Store` arm must not pay for. The last is shared with the rule's `Store` arm and the two transport sites, and it has to be here too: a cell this function drops is lost to every later route, because the two snapshots then differ at the read's own address. |
| `CMemory::without_field_cells` | disagrees | Same-block equality and a constant byte interval. Across blocks it removes too little, which for a copy is the safe direction; a completeness difference only. |
| `heap_allocation_may_contain_pointer`, `CMemory::freed_heap_allocation_may_contain` | disagrees | `base.block != pointer.block` answers "not contained", which is fail-open on a spelling. The rule's `HeapFreed` arm is two separation ladders instead. Reaching it needs a freed allocation whose base block is not proven distinct from a live cell's block. The second is the same test over every deallocated allocation, and it is what the zeroed drop, the availability check below and contract certification all read, so the spelling is at least in one place. |
| loop frame assembly `src/kernel/loops.rs`, `collect_loop_effect_check_obligations`, the multi-exit join | disagrees | Each reinstates or drops cells against the loop's *stated* effect summaries rather than a recorded edge, with a hardcoded `local:` skip. |
| `memory_diff_is_covered_by_pointers`, `memory_diff_is_covered_by_ranges` `src/kernel/proof/execution.rs` | another question | The containment direction: is every observed change *inside* the declared write set. The tracker has no containment question. |

### State versus state: "do these two snapshots agree about this read"

The tracker's `same` answers this for two points on one recorded history. These
sites answer it for two snapshots that need no ancestry — an effect summary's
endpoints, a recomputed chain, a canonical form — so `same` cannot replace
them without losing every pair the DAG does not connect.

| Site | Class | Note |
| --- | --- | --- |
| `c_memory_load_is_directly_unchanged`, `memories_directly_match_for_pointer_load` `src/kernel/memory_provenance.rs` | disagrees | The transport rule. It already asks the tracker as one disjunct — two snapshots that name the cell by one point hold the same cell — and the rest reads `CMemoryMutatesOnly`, `CMemoryEffectSummary` and `CHeapAllocationFreed` over *stated* endpoints. Its per-write ladder is the same four predicates the rule's `Store` arm uses, applied to a stated write list. |
| `memories_match_for_pointer_load` `src/kernel/reasoning/memory_resolution.rs` | disagrees | Assumption-free structural agreement about one load: the same forgotten-source identity; equal extents for every object the load may designate plus equal havoc markers; agreement about retirement tombstones and all load-observable heap lifetime, initialization and implicit-zero metadata; and equal cells and union cells under `observable_by_load`. Decides pairs with no common ancestor. |
| `memory_snapshots_match_for_resolution`, `memory_snapshots_proven_equal_at_pointer`, `memories_match_for_pointer_load_bounded_alias`, `memories_match_for_pointer_load_under_assumptions` `src/kernel/reasoning/memory_resolution.rs` | disagrees | The same question with assumptions: every cell the two snapshots differ on must both miss the load's bytes and be proven distinct from the load. All refuse a load whose own block is `local:`, and all select the cells to check with `cell_is_observable_by_load`, the one filter — *not*, as they used to, by dropping every differing `local:` cell unasked. See below. The second is a thin name for the first, so that a caller asking "are these two snapshots one state as far as this pointer is concerned" reads as that question rather than as a resolution internal. |
| `snapshot_objects_agree`, `retirements_agree_for_load` | separation | The object half, as against the values in the cells: an extent is what says an object is there and how big it is, and a tombstone is the only record that an automatic object's lifetime ended once its cells are gone. The first is the assumption-carrying comparisons' extent check, and the only extents it leaves out are the ones `local_block_no_pointer_can_reach` allows. The second is the tombstone check, which all four comparisons ask, and it allows a difference only where the load's block is proven distinct from the retired object or no pointer value in the program designates it — two exclusions, each catching what the other does not. A load through a stale alias is exactly the load these comparisons are asked about, which is why neither half may be skipped on a spelling. |
| `differing_cell_bytes_miss_the_load`, `differing_cell_byte_width` | separation | The byte half, asked of each differing cell before the address ladder may speak. A cell at `p + 1` holding one byte is a different address from `p` and is still the second byte a four-byte read there returns, so an address ladder alone is not an answer. The width is read from whichever side holds a value, the wider where both do and disagree, and the widest scalar where neither does, since over-stating a width can only shrink the separated set. |
| `memory_matches_effect_summary_endpoint` | disagrees | Whether a recorded effect summary's endpoint is the snapshot in hand: interned identity, else the assumption-free structural agreement above. An endpoint pair has no ancestry to walk, which is the whole reason this section exists. |
| `memory_load_terms_equal_for_fact_transport` | another question | Whether a fact about one load *term* is a fact about another: the two pointers proven equal, or one recorded offset equality between them, and then the snapshot comparison. A term question that ends in a listed state comparison, not a staleness decision of its own. |
| `memory_has_materialized_load_from` | another question | Whether one snapshot is the other with this load materialized into a cell — the cell holds exactly a load at this pointer from a snapshot the comparison then matches. A tactic that forces a symbolic load into a concrete cell mints such a pair, so the two are one state with different cells recorded, and both the pointerless equality and the per-load comparison ask it before they compare anything. |
| `canonical_memory_for_pointer_load` | separation | A normal form, so that two snapshots can be compared at all. Its filters are `observable_by_load` and `cell_disjoint_from_load_by_constant_offset`, one shared function each. |
| `memories_proven_equal_for_memory_resolution`, `memory_cells_definitionally_contained` | another question | Whole-state equality under assumptions, with no load pointer. The only `local:` cells and blocks either drops are the ones `local_block_no_pointer_can_reach` allows — see below. |
| `memory_range_still_available` `src/kernel/reasoning/path_facts.rs` | disagrees | Whether a memory fact established at one snapshot still describes an available region at another: the block present in both or absent in both, the same ended-local answer, and the same freed-allocation answer for its base. A staleness question decided from two states with no path between them, and about *availability* rather than about a version — the fact may be perfectly current and still describe storage that is gone. The freed-allocation half is what separates the two snapshots for an `ExternalArgument` allocation, whose block survives the `free`. |
| `differing_cell_pointers_possibly_aliasing` | separation | One call to `observable_by_load`. |

#### And the history has a veto over all of them

Every row above reads *state*. A cell map records what is known at a point,
and a canonical form drops what it can prove irrelevant to the load. Neither
records that a store happened, and a store into the middle of a cell drops
the cell it partly overwrote while the naming projection discards what it
leaves behind — so two snapshots a store separates can be identical
everywhere these sites look. Absence of a differing cell is not evidence that
no store happened, and reading it as such made `*q` provably equal to
`old(q[0])` across a one-byte write into the same `int32`.

So the loads' recorded history is asked first, and it can refuse. One
memoized query, `recorded_load_history` in `src/kernel/memory_provenance.rs`,
answers for a pair of snapshots and a pointer:

| Answer | What the history established | What the state routes may do |
| --- | --- | --- |
| one version | both cell walks reach one node, or one walk's store pins the other side's load | the equality is already proved; nothing else is consulted |
| different versions | a walk is stopped by a step `affects` reports `Affected` — a store whose bytes provably overlap the read, or the allocation, retirement or free of this very cell | nothing. The cell maps are not consulted for this pair |
| undecided | a walk ran out of history, or stopped at a step it could not classify | everything, exactly as before |

The answer is read off the two cell-source walks the equality question
already runs — `memory_dag_cell_source_with_stop` returns the node *and*
`CellWalkStop` — so asking the refutation after asking the equality costs a
memo lookup, not a traversal. Stated and assumed equalities never reach the
veto: the fact graph is consulted before the load arms are, at every site
that consults it, so a premise about the two values still outranks what the
history says about the cell.

The consumers are `loads_separated_by_recorded_history` for a pair of
snapshots and `load_equality_refuted_by_history` for a pair of terms, both in
`src/kernel/reasoning/memory_resolution.rs`. They reach the
`(MemoryLoad, MemoryLoad)` arm of the resolution equality, the deep
canonical-form comparison in `proves_atomic_without_search`, the origin-snapshot
comparison in `checked_origin_load_equality`, and the bounded matcher behind
`pointer_offsets_equal_after_exact_materialization`, so one store is seen the
same way by an integer goal, a pointer-offset goal and a 64-bit goal alike.
Where a comparison holds a naming projection rather than a derived snapshot,
`canonical_load_projection_source` leads back to the snapshot the projection's
materialized cells were loaded from, and the pair is asked again from there.

Two things the veto deliberately does not cover, both recorded here because
they are what a later repair has to start from.

A walk that stops at a step it could not show separate has proved nothing,
so the cell comparison still speaks. That is sound only while the comparison
can see the blocking store, and it cannot when a later possibly-aliasing
store has already dropped that store's cell from both snapshots: `a[i] = 7;
a[j] = 0; return a[m];` under `m != j` and nothing about `i` compares one
differing cell, separates it, and reads `a[m]` as unchanged. Making the stop
itself refuse is the principled repair, and it is not free: the walk's own
`Store` ladder is narrower in practice than the differing-cell scan, so a
blanket refusal withdraws field-derived and symbolic-index framing the corpus
depends on. The repair is to give the two one ladder, not to widen the veto.

Snapshots the history does not connect at all keep the structural comparison.
What that rests on is `memories_match_for_pointer_load`'s own state claim:
the same forgotten source, equal observable objects and heap-read metadata,
and equal observable cells. The forgotten-source check is essential because
a cell map is only knowledge layered over that source; identical empty maps
over two sources that stored different values are not one state. Object and
heap metadata matter even with no cached cell: they decide whether the load's
object exists, whether it is live and initialized, and whether calloc makes it
read as zero. The comparison filters each component with the same structural
may-alias rule as the cell scan, retaining global havoc identities and ignoring
only storage the load is proven unable to designate. This is a statement about
two states and not about any path between them; where no path exists there is
nothing for the history to say.

### The separation predicates, which stay one function each

`affects` has no overlap logic of its own; it asks these. They are listed so
that a fix lands in one of them rather than beside it.

| Predicate | Home |
| --- | --- |
| `PointerBlock::proven_distinct`, `may_alias`, `observable_by_load`; `Pointer::blocks_proven_distinct`; `block_is_never_address_taken_local` | `src/kernel/primitives.rs` |
| `pointers_proven_distinct_for_memory_resolution`, `pointers_distinct_through_one_exact_alias`, `never_address_taken_local_versus_pointer_value`, `pointer_offsets_with_common_base_proven_distinct` and its `_distinctness_condition`, `cell_disjoint_from_load_by_constant_offset`, `cell_is_observable_by_load`, `local_block_no_pointer_can_reach` | `src/kernel/reasoning/memory_resolution.rs` |
| `range_proven_disjoint_from_pointer`, `ranges_proven_disjoint_from_pointer`, `ranges_directly_disjoint_from_pointer`, `ranges_proven_disjoint_from_pointer_for_frame`, `frame_frontier_compositions`, `pointers_directly_disjoint_by_range`, `pointers_proven_disjoint_by_explicit_range_for_memory_resolution`, `pointers_proven_disjoint_by_shallow_explicit_range` | `src/kernel/assumptions/memory_reasoning.rs` |
| `typed_store_separated_ranges_evidence`, `typed_range_disjoint_from_pointer_evidence`, `typed_ranges_disjoint_from_pointer_evidence`, `heap_allocation_proven_separate_from_pointer`, `owned_composition_store_separated_evidence` | `src/kernel/memory_provenance.rs` |
| `memory_block_may_alias`, `memory_range_overlaps_pointer`, `memory_ranges_overlap`, `proves_resource_separate`, `proves_owned_range_separate_from_pointer_with`, `resources_structurally_separate` | `src/kernel/primitives/resource_algebra.rs` |
| `MemoryLoadAliasCache::resolution_distinct` | `src/kernel/eval/memory_loads.rs` — a per-load memo over the first of these, not a rule of its own |

#### The byte question, which is not one of them

Every predicate above decides whether two *addresses* are different, and that
is a weaker claim than the one a framing route needs. A one-byte store at
`p + 4` is a different address from `p` by every test there is, and it still
overwrites the upper half of an eight-byte cell read at `p`. So the answer the
routes conjoin with an address ladder is a separate function over the two
accesses' widths, `access_byte_overlap` (`src/kernel/reasoning/memory_resolution.rs`),
with `StoreByteInterval`, `cell_access_byte_width`, `one_element_gap_separates_bytes`
and `constant_byte_shift_between` beneath it. It has three answers, and the
third is the point: bytes provably separate, bytes provably overlapping, and an
unknown gap, which blocks the ladder rather than contradicting it.

It is in this list's neighbourhood rather than in it because it answers about
accesses and not about resources, and because it has no counterpart for the
cross-base pairs: two pointers with no common additive base get `Unknown`, and
those are exactly the pairs the range rungs exist to decide. The rule's `Store`
arm, `CMemory::without_possible_aliasing_cells` and the snapshot comparisons
all conjoin it, which is what keeps one store from being separate at one site
and overlapping at the next.

#### A load whose own block the verifier cannot resolve

`observable_by_load` is the filter the three load-framing sites above share, and
it used to carry one exception: when the *load's* own block was `Symbolic`, it
degenerated to `self == load`, a comparison of block names. A symbolic block is
a pointer value the verifier does not resolve, and `proven_distinct` separates
it from nothing, so that exception assumed exactly what the predicate exists to
deny. `mdtests/returned_pointer_may_alias_a_global.md` is the false theorem it
admitted: with `result == &g[0]` stated in the contract and in the context,
`a[0] == 5` survived `g[0] = 1`.

The exception is gone, and `observable_by_load` is now `may_alias` for every
load. Two things were `Symbolic` before, and only one of them still is:

- an object the verifier introduced, today the temporary that holds an
  aggregate a call returns by value, carries `PointerBlock::Temporary`. It is
  fresh — the program has no prior pointer into it and C gives it no way to
  take its address — so `proven_distinct` separates it from every other block,
  as it does `Heap`. Its loads keep the structural frame they had, which is why
  a struct-by-value result still reads correctly across an unrelated store with
  nothing added to the sidecar;
- a pointer value whose target is unknown — a returned `T*`, a callback result,
  a pointer loaded from storage the state does not hold, a branch join's
  selection — stays `Symbolic`, and a load through it now observes every cell
  not proven distinct from it.

Framing a load of the second kind therefore needs evidence, and one route
spends it: `pointers_proven_distinct_for_memory_resolution` takes **one hop**
through the index of assumed `PointerEqual` facts to a non-symbolic spelling and
asks the same question there
(`pointers_distinct_through_one_exact_alias`). `ensures result == &g[0]` and
`ensures result == p` are what that reads, and
`stored_value_at_equal_pointer` — which used to search only the load's own block
for a stored cell, and so answered "no stored value" for exactly those reads —
now filters by `observable_by_load` instead of by block name. A stated
*disjunction* of equalities needs no rule of its own: `simp` splits it and each
case holds its exact equality
(`mdtests/proof_branch_pointer_local.md`). The hop is substitution of equals,
so it is also what keeps the attack refused: resolving a returned `&x` moves the
read to `x`, which is not distinct from a store to `x`
(`mdtests/returned_pointer_to_a_caller_local_may_alias_it.md`).

##### The same shortcut, spelled on the other side

Withdrawing the exception from `observable_by_load` did not withdraw it
everywhere, because one filter of the same shape was written out by hand.
The three assumption-carrying snapshot comparisons —
`memory_snapshots_match_for_resolution`,
`memories_match_for_pointer_load_bounded_alias` and
`memories_match_for_pointer_load_under_assumptions` — check the cells two
snapshots differ on against the load, and each selected those cells with
`!cell.block.starts_with("local:")`. A differing `local:` cell was therefore
dropped before anything was asked about it.

That is the withdrawn exception with the sides swapped: instead of claiming an
unresolved load reads only its own block, it claims no local is a block such a
load reads. `&x` passed to a callee and returned is the counterexample in both
directions, and
`mdtests/an_unresolved_pointer_sees_the_store_to_a_local.md` is the false
theorem the second spelling admitted — the same C as the mdtest above with the
`ensures result == p` clause removed, so that no equality is involved at all
and only the framing decides. A store to a *global* was never skipped, which is
why the global attack was refused while this one was not.

The filter is now `cell_is_observable_by_load`, the one filter, and nothing is
lost where the skip was sound: a load whose own block is `local:` is refused by
all three before they reach it, and every other block a store can name —
`ExternalArgument`, `ExternalObject`, another `Concrete` block, `Heap`,
`Temporary` — is proven distinct from a `local:` block, so those cells are
answered on the first rung of the ladder rather than skipped.
`a_store_to_a_local_is_not_framed_away_for_an_unresolved_pointer`
(`src/kernel/tests/memory_reasoning_tests.rs`) pins the history directly.

The cells were only half of what these comparisons hold. Beside them sits the
object map — each block's extent, and the tombstones that say an automatic
object's lifetime has ended — and it carried the shortcut in its own spelling:
the three assumption-carrying comparisons compared the extent of every block
*not* spelled `local:`, and none of the four compared the tombstones at all. An
extent is what says an object is there and how big it is, and a tombstone is
the only record left once the object's cells are gone, so two snapshots
disagreeing about either disagree about what a load through a pointer that may
designate it reads. The extent check is now `snapshot_objects_agree`, dropping
only what `local_block_no_pointer_can_reach` allows, which is the same thing
the pointerless equality below spends; the tombstone check is
`retirements_agree_for_load`, which all four ask, and which allows a difference
only where the load's block is proven distinct from the retired object or no
pointer value designates that object at all.

##### And the same shortcut with no pointer at all

Two neighbours carried it a third time, and neither had a load pointer to ask
`observable_by_load` about: `memories_proven_equal_for_memory_resolution` and
its certification twin `c_memories_definitionally_equal`, whole-snapshot
equalities that each dropped every `local:` cell and block before comparing.

The one caller that decides a *load* question with them has a pointer and now
passes it. `PureFactContext::has_order_path_for_memory_resolution`
(`src/kernel/assumptions/condition_reasoning/order_paths.rs`) hops an order
path through an assumed equality, and its `order_terms_match` asks whether two
`MemoryLoad` terms at one pointer are the same term. That is exactly the
question `memory_snapshots_proven_equal_at_pointer` answers, so it asks it
there, and the two disjuncts it had — the pointerless equality, plus the
bounded per-load bridge that a whole-memory equality needs across a call's
havoc block — are both inside that one function. The only pairs it stops
accepting are the ones the shortcut was wrong about: for a load whose pointer
is in another `local:` block, or in `ExternalArgument`, `ExternalObject`,
`Heap` or `Temporary`, a differing `local:` cell is answered on the first rung
of the distinctness ladder rather than skipped, and what is left over is a
load through a pointer nothing resolves, or one in the differing cell's own
block — which is the case the comparison exists to decide.

What is left is genuinely pointerless. The remaining callers of
`c_memories_definitionally_equal` — the effect-chain endpoint checks in
`checked_interface_effect_facts`, the resource-rewrite and
resource-observation evidence checks in `src/kernel/proof/execution.rs`,
`function_entry_representation_states_match`, the two outcome comparisons and
the recomputed-havoc matcher — are comparing two whole states with no read in
hand. They may still skip a `local:` block, but only for the reason that needs
no pointer, and that reason is one function:
`local_block_no_pointer_can_reach` (`src/kernel/reasoning/memory_resolution.rs`)
is `primitives::block_is_never_address_taken_local`, so the only automatic
objects a pointerless comparison ignores are the ones no pointer value in the
program designates. Both comparisons and both of the twin's own filters read
that one function, so the kernel and the certification side cannot drift.

The object read under **its own name** is a different question and not this
filter's: a scalar local's program-visible value is in the `CLocalEnvironment`
binding, which these callers either compare exactly as part of `CState`
equality or do not ask about, and a caller that needs the slot cell compares
`CState::local_cell_values` beside the memory, as
`function_entry_representation_states_match` does.

No witness was found for the shortcut in either place, and that is a report
about the other locks rather than an argument. The order-path caller is
reached only from the two rules that place an index in a range —
`bitvector_index_in_range_shallow` and
`element_delta_in_range_by_affine_arithmetic` (`src/kernel/assumptions.rs`) —
so the load would have to be
a range bound; reading through an unresolved pointer in *executed* C needs a
`views`/`owns` resource fact the caller of such a function does not hold
(`missing resource fact views symbolic-pointer:…`), a local array cannot be
lent to a callee that `owns` it (`missing resource fact owns local:arr@…`), and
the value equality itself no longer transports, because
`bitvector_terms_proven_equal_for_memory_resolution` already asks about the
pointer. The certification twin's callers validate recorded sidecar evidence,
which a surface program does not author. A kernel filter that is sound only
because three other checks happen to refuse first is not sound; the
regressions are the two polarities in
`a_pointerless_snapshot_equality_drops_only_a_local_no_pointer_can_reach`
(`src/kernel/tests/memory_reasoning_tests.rs`), where a snapshot pair differing
in an address-taken local is not equal — for the pointerless comparison, for
its certification twin, and for a symbolic-pointer load — while a pair
differing only in a local no pointer can reach is.

One relative of these two is deliberately wider and stays so:
`c_effect_memories_definitionally_equal` strips *every* local from both sides
before comparing, because an effect memory is the externally visible state an
effect summary is about. That is a statement about what the comparison is for,
not a shortcut inside it.

##### The local nobody can point at

The commonest read there is — `p = f(); … p[0]` — has no contract to appeal
to. The store of the returned pointer into the caller's own `p` is itself a
step the read must be told apart from, and `p` belongs to the caller of the
function whose contract is being written, so nothing a contract can say
mentions it. `proven_distinct` says nothing either: a `Symbolic` block is
separated from nothing.

The claim that decides it is about *addressability* rather than about one
pair of pointers. C offers exactly two ways to obtain the address of an
automatic object — the `&` operator and the array-to-pointer conversion of an
aggregate object's name — so an object neither of them reaches is storage no
pointer value in the program designates. Nothing else can reach it either:
arithmetic that leaves the object it was derived from is undefined behaviour
that Click refuses on every displaced access (`CMemoryCanStore` /
`access_in_bounds`), and an integer cast to a pointer is outside C0. An `&x`
written in a *proof* creates no runtime pointer.

`src/languages/c/address_taken.rs` is the one conservative syntactic pass
that decides it, run over every parsed body before any query, and
`primitives::block_is_never_address_taken_local` carries the argument for
spending its answer. The pass is default-deny in both directions: a name is
reported only if every declaration of it is scalar or pointer typed and it
never occurs below an address-forming node, and anything the walk cannot
account for is simply absent, which is the same as addressable. The rule
itself is the last disjunct of
`pointers_proven_distinct_for_memory_resolution`, after every cheaper check,
and costs one lookup on a bounded name.

Two things follow from where the answer is kept.

- It is a set of **names**, program-wide. A `local:` block says nothing about
  which function declared it — `local:x` in `f` and in `g` are one spelling —
  while the resolution memo and the canonical-projection cache are scoped per
  verification, not per function. A per-function answer would be cached under
  whichever function asked first and served to the next.
  `mdtests/a_local_addressed_in_another_function_is_not_framed.md` is what
  that costs: one `&guard` anywhere loses every `guard`.
- It is safe on the **naming** walks, which carry no facts, because it is a
  property of the whole program's source rather than of one proof path. That
  is the opposite of a composition fact, below.

The regressions are `mdtests/string_literals_call.md` and
`mdtests/a_returned_pointer_reads_across_stores_to_caller_locals.md` on the
true side; on the false side the four ways an address escapes —
`an_unresolved_pointer_sees_the_store_to_a_local.md` (`&x`),
`…_to_a_local_array.md` (array decay), `…_to_an_addressed_field.md`
(`&s.first`), `…_to_an_addressed_parameter.md` (a parameter's `&`) — plus
`an_address_parked_in_storage_is_still_an_address` in
`src/languages/c/address_taken.rs`, where the address never comes back from
the call it was handed to.

##### Two owners are two places

The other evidence a contract can state is a **separating resource
composition**. `owns value[0..1]` beside `owns Cell(result)` in one context
says the two hold disjoint bytes; `value` is an `ExternalArgument` address and
`result` is a pointer a callback returned, so nothing structural relates them
and no offset cancels, and ownership is the only thing that tells them apart.

`memory_provenance::owned_composition_store_separated_evidence` is the rule:
a store is separate from a load when one composition in the context owns the
written address and the read address through **different members**. Three
things make it the narrow claim it is.

- **Two owners, never an owner and a view.** The rule reads
  `memory_own_range`, so a viewed member contributes nothing. That is not
  conservatism, it is the invariant: `MemoryResourceAlgebra::pair_validity_error`
  refuses only *owner/owner* overlap (`OverlappingOwnedMemoryResources`), and
  says in as many words that an owner overlapping a view is decided by the
  view's binding, which it cannot see — an unbound view beside its owner is an
  observation of that very ownership (`owner_observation_core`) and perfectly
  valid. `observable_facts_assuming_valid` states the half that is a law:
  "two owned members are pairwise separate".
- **A claim about addresses, not about state.** What two members yield is that
  two address ranges do not overlap, and an address is a value: each range is
  spelled with pointer terms whose loads carry their own snapshot. A store
  cannot move the bytes a range named, and consuming, transferring or freeing
  a resource cannot make two ranges that were disjoint coincide. So a
  composition recorded at an earlier program point is as true later as it was
  then — which is why the rule does not need the resource to still be held,
  and why the retained hop names the composition as its premise all the same.
- **Facts only, never a name.** Composition facts are path facts. The rule is
  spent exactly where a typed `separate(..)` is spent — the fact-consulting
  route — and the two naming walks cannot reach it, because both are handed
  `PureFactContext::new()` (`resource_tracker::cell_source_for_naming` and the
  block-epoch walk) and an empty composition set decides nothing. On the
  querying route the answer is re-derived per query, keyed by the context
  (`resolution_query_memo_id`), and never written onto an interned edge.

It sits **last**, after every cheaper check, at the four places the
store-versus-load question is asked: the tracker's `Store` arm, the two
transport sites in `memory_provenance` (`memories_directly_match_for_pointer_load`
and the `CMemoryMutatesOnly` arm of `c_memory_load_is_directly_unchanged`), and
`CMemory::without_possible_aliasing_cells`. The last of those is the one that
decides `c_contract_executes_acquire`, and it is not optional: once a store has
dropped a cell, the two snapshots differ *at the read's own address*, and no
later framing route can recover it. It is kept beside
`pointers_directly_disjoint_by_range`, which is at that site for the same
reason, and it does **not** expand composites — `frame_frontier_compositions`
stays off this path, which is what the comment on
`ranges_proven_disjoint_from_pointer_for_frame` asks for.

Cost: an emptiness gate first, then two block-bucket lookups per composition
held, no pair materialization and no expansion.

`CMemory::without_possible_aliasing_cells` also asks the same law *first*, in
an indexed form. Every pointer parameter shares the one `ExternalArgument`
block, so neither `AliasCandidates` nor the block-pair separation index
narrows a store through one parameter, and every cached cell of every other
parameter reaches the ladder, where the range rungs fail slowly: each failing
search walks the composition's projected pairs, which grow with the square of
the owned objects. So the store computes once which owned members hold its
written bytes (`PureFactContext::owned_store_footprint`), and each cached cell
then asks whether a *different* member of one of those compositions holds all
of its bytes (`access_owned_apart_from_store`). Both lookups go through each
composition's `memory_by_base` index under the additive base spellings of the
address (`p`, `p + f`, `p + i·w` and their left spines), never a block
bucket, and membership is the structural route only — base, or base plus
one displacement — with the two endpoint bounds proved; the whole access must
fit, not just its first element. The guards are the ones above: the two
addresses must not be proven equal, and ranges whose base spellings were
later proven equal must not overlap. A cell the rung does not place goes
down the ladder unchanged, so a miss costs time and never a decision.
`a_store_beside_owned_parameter_fields_is_linear_in_the_cached_cells`
(`src/kernel/tests/memory_scaling_tests.rs`) is the regression: 96, 160,
288, 544 units at 4, 8, 16, 32 cached parameter fields, where the ladder
alone charged 376, 1508, 8732, 60940.
`a_store_through_one_parameter_forgets_another_unless_ownership_separates_them`
and `a_cell_straddling_two_owned_members_is_not_separated_from_either`
(`src/kernel/tests/memory_reasoning_tests.rs`) are its attack set.
`stores_beside_many_owned_ranges_scale_near_linearly`
(`src/surface/tests/scaling_tests.rs`) is the deterministic regression: the
query's own work over 2/4/8/16 stores is 9, 11, 15, 23 units.
`a_composition_separates_a_store_from_a_load_only_through_two_owners`
(`src/kernel/tests/memory_reasoning_tests.rs`) is the attack set — an owner
beside a view, a cell past the end of every member, a folded composite whose
body would cover the cell, a single member asked to separate an address from
itself, and a retained hop offered to a context that no longer holds its
composition.

##### The entry partition

The composition rule above must *not* be widened to cover
`mdtests/const_callback_field.md`. `read_view(struct reader *r, const int *p)`
holds `owns object(r)` and `views p[0..1]`, both spelled in one `external`
block with symbolic offsets, and its claim is true: a caller cannot both
transfer `object(r)` and lend a window inside it, because suspending the write
authority for the loan leaves no usable copy to transfer
(`docs/internals/stable-views.md`, law 1, and "usable ownership and an active
independent view of overlapping memory cannot coexist"). But that is a
statement about the `views p[0..1]` **clause**, and the context the body proof
runs under also holds `views r[0..2]` beside `owns r[0..2]` — an owner
observation of the very range it describes. Owner-beside-view therefore cannot
mean separation; the discriminator is the origin of the clause.

So the rule is written over clauses. The **entry partition**: a contract's
transferred memory clauses (`owns`/`consumes`) and its *borrowed* memory
clauses (a `views` clause the caller lends) denote disjoint memory, so a store
through one is framed from a load through the other. It holds the way the
ownership partition itself does — inductively, with the outer boundary as an
environment assumption.

Every way a contract can be entered checks it, and each check is **fail-closed**:

| Entry | Where | Checked by |
| --- | --- | --- |
| an ordinary call, a self-call (recursion) | `prepare_function_resource_transfer` → `prepare_contract_resource_transfer` `src/kernel/functions.rs` | `plan_stable_view_transfer_with_bindings_and_composites`: exclusive requirements are reserved out of the caller's `residual` *before* any view is planned, and each view's backing owner must still be found in that residual (`ConflictingRequirement` → `ProvenOverlap`) |
| a call through a function pointer or a `contract` interface | the same funnel, from `execute_c_function_call_paths` and the contract-transition sites | the same planner |
| contract/implementation refinement | `prepare_contract_resource_transfer(.., "refinement", ..)` | the same planner |
| the contract's own entry, for the body proof | `install_borrowed_contract_inputs` `src/kernel/api.rs` | a viewed clause that provably overlaps an owned clause, or that the contract's own resources already own, is refused (`protected_range_proven_overlapping`, `directly_supporting_owned_entry`) |
| the outer boundary | — | an **assumption** about the environment, in the same class as the ownership the contract also assumes: a precondition's clauses are read as a separating conjunction |

There is no thread or fork/join entry on master. The entry self-check is
fail-*open* (`protected_range_proven_overlapping` refuses only a *proven*
overlap), which is exactly why the call-site planner has to be fail-closed,
and it is: a caller that cannot prove the lent range sits inside an owned
entry it still holds is refused for want of backing, not admitted.

Measured, on the minimized `split(int32* a, int32* b) { owns a[0..1]; views
b[0..1]; }`:

- `split(g, g)` from a caller holding `owns g[0..4]` — refused, *"a required
  resource overlaps a live borrowed footprint refused during planning;
  selected resource `owns global:g@0[0..1]`"*;
- the same through a function pointer under `contract Split` — refused
  identically;
- `split(g, q)` where the caller holds `owns g[0..4]` and nothing about `q` —
  refused, *"the required loan backing or binding is missing … `views
  q[0..1]`"*;
- `split(g, q)` where the caller also holds `views q[0..1]` — accepted, which
  is the induction step: the callee's pair is a reborrow of the caller's own
  pair.

###### Where the fact lives

It needed no new fact kind and no new framing route. At contract entry, each
(transferred memory clause, borrowed `views` clause) pair of one contract
yields the ordinary explicit separation `separate(memory(X), memory(Y))` —
`Proposition::CResourceSeparate` over two `CResource::Memory` operands, exactly
what a written `requires separate(memory(a[0..n]), memory(g[0..1]))` lowers to
(`mdtests/a_separated_array_argument_survives_a_global_store.md`). The Store
ladder therefore spends it at `typed_store_separated_ranges_evidence`, where it
spends a stated one, and the havoc side reads it at
`typed_range_disjoint_from_pointer_evidence`.

`functions::contract_entry_partition_facts` is the rule, and it reads the
contract's evaluated **clause list** — the `Vec<CCheckedResourceFact>` that
`evaluate_function_resource_context_with_metadata` returns, one fact per
written clause — never a context. That is the whole discriminator: a context
holds the owner observation above, and the clause list does not.

The resulting separation remains path evidence, not a permanent address fact.
A later equality can make its two ranges overlap while the original
`CResourceSeparate` proposition remains in the context. Before an indexed
separation candidate can be used, `PureFactContext` now compares the ranges'
current bases using path equalities that do not consult separation evidence,
then checks their byte intervals; an overlapping or undecidable pair cannot
justify separation. `StoreSeparatedRanges` evidence repeats that check when a
retained hop is consumed. This breaks the circular case where the stale
separation would otherwise veto the equality that invalidates it.
`entry_separation_does_not_frame_a_store_after_its_bases_become_equal`
(`src/kernel/tests/memory_dag_tests.rs`) pins both evidence production and
rechecking of an already-retained hop.

Four pairs it does not build:

- **an owner and the observation of its own range.** Not in the clause list,
  so it never reaches the rule;
- **two borrowed views.** Two `views` clauses may overlap freely; lending
  twice is what a shared borrow is;
- **two owners.** That is `owned_composition_store_separated_evidence` above,
  and a second spelling of one rule is a second place a fix has to find;
- **a clause that is not plain memory.** A composite's owned footprint is its
  expansion, and `separate(memory(..), memory(..))` cannot name it without
  expanding it, so the pair is skipped outright rather than approximated.
  `owns object(r)` is *not* such a clause: `object(r)` lowers to the plain
  range `r[0..size/4]`, which is what makes `const_callback_field` expressible.

The two sites that know they are at a contract entry produce it independently
from the same list, so neither trusts the other: the body proof's
`initial_claim_context_with_caller_owner` (`src/surface/proof.rs`), and
`contract_certification::c_function_contract_certification_assumptions`, which
authorizes such an entry premise as derivable from the contract's own clauses
the way it already authorizes a `viewable` one from the resources those clauses
supply. Emitting instead at `ResourceContext::observable_facts_assuming_valid`
— the one point the two sides share — was the shape rejected: it sees a
context, not an entry, and would assert the partition for every bound view in
every context, which is a strictly larger claim than the one above.

The caller owes nothing new. The fail-closed planner is what discharges the
assumption, and it already runs at every call.

###### What may not read it

A check that decides the partition may not consult a claim of it. Two
questions short-circuit on an explicit memory separation —
`memory_ranges_proven_overlapping` answers "not overlapping" and
`memory_range_covers` answers "does not cover" as soon as the context holds
one — and the entry partition is exactly such a separation over exactly the
clauses those questions are about. So `install_borrowed_contract_inputs` asks
both of its halves (`protected_range_proven_overlapping`, and
`directly_supporting_owned_entry` for a view the contract already owns) under
assumptions with *every* explicit memory separation removed. Dropping them all
rather than the derived ones by name means nothing rests on the two producing
sides spelling one fact identically, and it can only make that check refuse
more. `root_view_refuses_an_owned_alias_of_the_viewed_range`
(`src/surface/verification.rs`) is the regression: `requires q == p; views
p[0..1]; owns q[0..1];` stopped being refused when this was missed.

The other check of the same family needs no such care, because of the order
things happen in. `MemoryResourceAlgebra::pair_validity_error` refuses two
*owned* ranges that overlap, and it runs while the clause list is composed —
which is what the facts are derived from, so at that point they do not exist.
Both producing sides evaluate the clause section before they build the
partition, so the composition that yields the facts is always validated
without them.

Cost: at most `#owned × #viewed` clauses of one contract, built once at that
contract's entry and never on a query path. A pair whose two blocks are
already `proven_distinct` is skipped: every memory separation the context
holds is one more entry in the block-pair bucket each coverage and overlap
query walks, so recording an answer those queries reach anyway is paid for on
every query and buys nothing. An `ExternalArgument` range beside a global is
not such a pair — an argument may point at the global — so the skip is narrow.

The attacks are `mdtests/a_caller_cannot_lend_and_transfer_one_range.md`,
`…_a_function_pointer_caller_…` and `a_self_call_cannot_lend_and_transfer_one_range.md`
on the call side; `an_owner_is_not_separate_from_its_own_observation.md`, where
a store through the owner is still seen through the owner's own observation
view; and `an_entry_view_names_the_entry_address.md`, where a `views
p->buf[0..n]` clause is followed by `p->buf = other` and the read through the
*new* `p->buf` is not separated, because the fact names the entry address. The
clause-list pairing itself is pinned by
`the_entry_partition_pairs_a_transferred_clause_only_with_a_borrowed_one`
(`src/kernel/tests/memory_reasoning_tests.rs`). On the true side,
`const_callback_field.md` is unquarantined,
`a_views_clause_is_separate_from_an_owns_clause.md` is the minimal shape, and
`pointer_params_separate_by_transfer_and_loan.md` is the two-parameter one.

Loop `owns`/`views` clauses are **not** part of this. A loop head is not a
contract entry: there is no call-site planner between an iteration and the
next, so the induction above does not run, and a loop's clause list gets no
partition facts of its own. A function's entry facts reach its loops the way
every other entry fact does, as path facts of the context the loop starts from.

The loan family — `LoanLedger::permits_memory_access`,
`protected_range_proven_overlapping`, `active_memory_overlaps` — is **not** in
the entry table above. It is fail-open by design and its soundness rests on the
ownership partition rather than on the predicate (`src/kernel/loans.rs`), so it
must never be merged with the fail-closed families there.

### Sites that only look like this question

`may_refer_to_memory_block` (resource selection before
`is_proven_separate_from_allocation`), the `held_child_witness` block filter
(witness naming for a `fold`), `is_external_memory_pointer` (evaluation
classification), the `local:` authority gates in `src/kernel/api.rs` and
`src/kernel/functions.rs`, `is_preexisting_write_pointer`, and the block
comparisons in `src/surface/diagnostics.rs` all compare block identities
without deciding staleness. Two carry a residual risk worth naming:
`may_refer_to_memory_block` compares a block by spelling before the proof-based
allocation-separation check runs, so a caller resource spelled differently from
a retired allocation is skipped rather than refused (the call rule draws the
same selection from the resource indexes, through
`ResourceContext::facts_that_may_refer_to_memory_block`, so its cost is the
retired block's candidates and not the caller's whole frame); and the
`held_child_witness` filter accepts `own.block != pointer.block` as "a
different pointer" with no proof, which selects a witness rather than proving
anything.

## What stays out

Three things the tracker is deliberately not asked, because they are about
authority — "may I touch this" — rather than about versions:

- **resource occurrence identity** (`ResourceOccurrenceId`) and the **loan
  ledger**. Loans, shares and support bind to an occurrence; no proposition can
  name one, and the ledger's `LoanLedgerStateId` is opaque and carries no delta.
  The loan family is fail-open by design and must never be merged with the
  fail-closed families (above, and `src/kernel/loans.rs`);
- **resource validity** — `pair_validity_error`, `permits_memory_read` — which
  is who may touch a footprint, not which version it holds;
- **separation predicates**, which `affects` calls rather than replaces.

A **C local scalar binding** has no version either: a fact about a local is a
fact about the value term substituted at lowering. Whether eager substitution is
the final answer there is open.

## Next chunks

- **Chunk 2** — one question, asked one way. The step-side deciders are one
  rule now; what is left is settling the block column's remaining blanket
  refusals, one commit and one regression each.
- **Chunk 3, next slice** — `last_same` over a chain for the saved-state kinds.
  It needs a recorded history of resource-context changes that names the step
  that made each one; today `ResourceContextChange` records *which facts*
  changed and never what changed them. Until that exists, two-point
  `same_at_states` is the whole resource-side interface, and the step comes from
  the mint.
- **Chunk 3, also unrouted** — the proposition-level refusals (`simp_failure`,
  and an unclosed `have` whose goal matches an available fact up to a model-field
  version) print the field's source spelling now but do not yet reach
  `describe_resource_version_mismatch`: their callers hold two propositions and
  not the two saved states the answer needs.
- **From the map above** — the two duplicated retain closures are one function
  each now, `call_havoc_keeps_cell` and `loan_preserving_havoc_keeps_cell`, so
  a producer and the checker that re-derives it can no longer drift apart by
  an edit to one of them. `call_havoc_keeps_cell` now requires range-disjointness
  evidence when a local cell has a differently spelled range base; direct
  same-block construction transitions retain their existing behavior, while an
  assumed-equal alternate spelling drops the cached cell.
  The remaining *disagrees* entry is the difference between plain range
  disjointness and the rule's typed range evidence plus `_for_frame` composite
  expansion.
