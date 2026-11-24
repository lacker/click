# The resource tracker

The resource tracker is the one place in the kernel that knows **which
resources are known to be the same at which program points**. It is an
internal Rust interface. It adds no Surface Click syntax, no tactic and no CLI
command, and it does not change which C programs Click accepts.

It exists because that question was already being asked in several places,
each with its own walk and its own answer, and because the answer a walk threw
away — *where* it stopped and *why* — is exactly what a user needs when a
proof fails with two terms that print alike.

## The vocabulary

- **resource** — a piece of mutable state, or part of one. Today: a memory
  cell, a memory block as a pure function reads it through an array argument,
  and one model field of a resource instance. A byte
  range, a struct object and a local are the kinds that come next.
- **program point** — a node a proof path reached, named by the location or
  proof mark passed to `at`. The kernel represents it with `ProgramPoint`,
  for now identified by the interned memory state there. `RecordedStates`
  associates a named point with a symbolic execution state on this path.
- **version point** — the point a read is lowered to. The assumption-free
  version walk selects one for the resource being named. Reads at distinct
  points can share one version point for one cell.
- **state point** — a borrowed `StatePoint` handle to an `ExecutionState`,
  used to compare model fields whose versions are symbolic values.
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
last_same_version_point(resource, at) -> Option<ProgramPoint>        // the naming path
cell_value_on_path(at, pointer, bytes, facts) -> Option<ProgramValue> // a C read, on one path
```

`Sameness` is `Same`, `Changed { at, by }` or `Unknown { at, why }`. `Stop`
pairs a `Change` — what happened at the point the walk stopped at: a store to
an address, a call's havoc with its write set, a loop's havoc, a free, an
allocation, a declaration, a lifetime end, cells forgotten, the beginning of
the history — with a `StopReason`: the step `Affected` the resource, or it was
`NotShownSeparate` and by which `SeparationCheck`, or the history ends there.
The history's beginning is the `function.entry` point: the root a proof path
starts from, below everything entry construction records
([memory derivation DAG](memory-dag.md)).

`Resource` is borrowed, so asking costs the same as the walks cost before.
`Explanation` is bounded: the resource, the answer, and how many recorded steps
the tracker crossed after the blocking one. It never carries memory.

## Two kinds of point, because there are two kinds of version

A memory resource's version is named by its **version point**: the memory
state selected by the assumption-free walk, where an operation last changed
the cell or prevented the walk from proving it unchanged. That is what makes `last_same_version_point` a naming path — a load
variable's name can embed the point, and equal names then mean equal terms.

A model field's version is the **value stored in the instance**. It is not a
point on the memory history: a `fold` changes resources and not memory, and a call that
returns ownership keeps the instance's identity while replacing its field
vector. So its points are whole saved states — `StatePoint`, a *handle* to a
state the kernel already keeps (`entry`, a `mark` out of `RecordedStates`, a
loop's iteration state, the live one), never a copy.

```rust
same_at_states(resource, left: StatePoint, right: StatePoint) -> Sameness
explain_at_states(resource, here, there) -> Explanation
```

Three decisions are worth writing down.

- **A field's version is its stored value**, with no generation counter and no
  new per-instance state. An instance that survives a call keeps its identity
  and gets fresh field variables, so the stored value already distinguishes the
  versions. Adding a counter would be a second answer to a question the state
  already answers.
- **It answers `Unknown`, never `Changed`.** `Changed` is what a recorded write
  earns, and no `MemoryDerivation` edge carries "field *k* of this instance was
  replaced". The *step* is still named, but it is read from the mint rather than
  from a walk — see below.
- **It fails closed.** `Same` needs both lookups to succeed and the two values
  to be syntactically equal. A missing instance, a
  parent-qualified path this lookup does not resolve, and two different
  forms of one value all answer `Unknown`. A tracker that answered `Same`
  for a field a contract did not promise would verify a false theorem.

`last_same` and `last_same_version_point` return `None` for both kinds, exactly as they
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

The same registry is what lets a refusal print `v1000002` as `c.rank`, and the
entry model as `old(c.rank)`, in the one place terms are printed
(`describe_bitvector_with_context` and `proof_diagnostics::render`). The
instance's own name comes from the surface, which registers it where it resolves
a field access and where a verified function declares its binders; a name only
half known prints nothing, because a half-printed field would look like source
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
(`src/scaling_tests/kernel/resource_tracker/tests/saved_states.rs`) grows both states by unrelated
instances over 8, 16, 32 and 64 and asserts two units
at every size, with the answer checked each time. Deterministic work for a
passing proof was unchanged to the unit: the named-operation totals of
`rb_replace_node_with_children` and two since-replaced mdtests were identical
with and without this chunk.

`last_same_version_point` is the only form on the hot path. It is what a term that
reads memory is named by: a load variable embeds the oldest point its cell is
the same as, and an array argument carries the oldest state that still
agrees about its block, so equal names mean equal terms. The stop information
is *computed from the point the walk stopped at* rather than recorded along the
way, which is why naming pays nothing for it.

For static storage, the memory arena maintains a persistent map from the
changed block to its version. It extends the map when a derivation is
recorded, using that edge's named object or checked write set. A barrier
supplies the default version for the next suffix. When a loaded pointer
needs the ordinary block rule, the walk starts at that edge and skips the
suffix already covered by the index.

Naming walks ask their questions in one empty fact context per verification
session (`naming_context`). It holds no fact, but an alias question still
registers the queried pointers, and the producer-recorded reads their
addresses depend on, in the context's equality graph. A fresh context per walk
registered a load's whole chain of address reads again at every call it was
named after, so a call step's cost grew with how deeply its arguments were
reached (`naming_a_load_after_a_call_is_flat_in_its_address_read_depth`). The
shared context registers each read once, and is rebuilt when a session restore
replaces the logical-read table it reads.

`cell_value_on_path` is the one question asked under a path's facts, and it
names nothing. A store at an address the facts could not place when it ran —
`buf[u] = 7` — drops the cached cells it may write, so a later C read of
`buf[0]` finds no cell even on a path that has since learned `u != 0`, and the
naming walk, being assumption-free, stops at that store. The C load asks this
before it mints a load term: where the naming walk stops, `affects` is asked
about the stopping step under the path's facts, and on a separate answer the
memoized naming walk resumes from the step's base. The answer is the value the
state it lands on caches at exactly the read's pointer; with no fact that
places the store, or one that puts it on the cell, there is none. The work is
one memoized naming lookup and one separation check per step the naming walk
cannot cross. A file-scope array used to get the same answer by accident: its
reduced memory re-interned as the state before the store, which a heap
store's initialization record prevents.

## What it is not

- It has **no ownership rules**. It never decides who may read or write a
  resource. It has no overlap logic of its own: it asks the resource and
  assumption layers whether two footprints are separate.
- It **never looks inside a proposition**. A term matters to it only through
  the resources the term reads; a fact only through its terms.
- It **does not search**. Every question is a bounded walk over recorded
  history with exact lookups, so it gives the same answer wherever it is asked.

## The soundness corridor

The tracker reads `MemoryDerivation` edges (`docs/internals/memory-dag.md`).
Interning is first-wins, so one edge can be shared by proof paths with
different assumptions. An edge may therefore carry only what is true on
*every* path that could produce that state: a write set qualifies, a
path-dependent separation does not. The two naming walks are consequently
assumption-free — an answer that is embedded in a name and memoized per
interned state must not depend on one path's facts — and the evidence for
crossing an edge is re-derived in the querying context instead of being stored.

The mirror rule holds on the query side: retained evidence names premises,
never a context (`docs/internals/proof-objects.md`).

The two version memos (per `(retained_state, pointer)` and per `(retained_state, block)`)
are cleared with the other canonical-form caches when a `VerificationSession`
starts, because interning dedups by content and one verification's history
must not answer the next one's question.

Bounded cell-source checking does not consult those version memos. Each hop
records one actual transition; a warm history result cannot stand in for a
sequence of transitions or change whether a simple step succeeds. Longer
preservation arguments must be supplied explicitly, for example through
`preserve(...)`. The cache-independence regression queries the same
read before and after warming the naming cache and requires identical results.

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
| `Store` | separate on proven-distinct blocks, a common-base offset inequality, checked full-byte separation through a base alias, typed `separate(..)` evidence, an explicit range, general distinctness, or two owned members of one composition | separate **only** on `AddressBase::proven_distinct` | separate when the written bytes miss every range |
| `BlockDeclared` | separate under the extended-bridging gate: it writes nothing | separate when the declared object is proven distinct: it has its own `blocks` key, so this block's size is the entry it was | separate: it writes nothing |
| `HeapAllocationPending` | separate under the extended-bridging gate | separate: a request with no address yet records nothing a read of a block consults | separate: it writes nothing |
| `ContractAllocationClaimsChanged` | separate under the extended-bridging gate | **stops** | separate: it writes nothing |
| `ContractAllocationRetired` | separate when the possibly released allocation misses the cell, or, on every path including naming, when the retiring call's own havoc covers the whole allocation | separate when the allocation's object is proven distinct | separate when its bytes miss every range |
| `ObjectInitializationRecorded` | separate under the extended-bridging gate: it records metadata without writing bytes | separate when the initialized object is proven distinct; stops on that object because its initialization status changed | separate: it writes nothing |
| `CellsForgotten` | separate under the extended-bridging gate | **stops**: the state is the same, the cell map is not | separate: it writes nothing |
| `HeapAllocated` | separate under the extended-bridging gate when the block differs | separate when the fresh object is proven distinct | separate: a stated footprint names objects that already existed, so the fresh one's bytes are in no range of it |
| `LocalLifetimeEnded` | separate under the extended-bridging gate, on general distinctness | separate when the retired object is proven distinct | separate when the retired object is proven distinct from the object every range is in |
| `HeapFreed` | separate on two separation ladders, both inside the extended-bridging gate | separate when the released allocation's object is proven distinct | separate when the released bytes miss every range |
| `CallHavoc` | separate on range disjointness, or when a range the caller kept owning holds the cell | separate when every declared range's object is proven distinct | separate when every declared range misses every range |
| `LoopHavoc(Some)` | separate when every declared range's object is proven distinct; otherwise only under the extended-bridging and explicit-check gates, and never on the naming path | separate when every declared range's object is proven distinct | separate when every declared range misses every range |
| `LoopHavoc(None)` | never separate | never separate | never separate |
| `BranchJoin` | separate when checked paths from every incoming arm preserve the full byte range back to their common history | stops conservatively | stops conservatively |

Two kinds still refuse a block outright, and both for want of a name on the
edge: `ContractAllocationClaimsChanged` names no allocation, and a contract
claim may cover a subrange of `ExternalArgument` memory; `CellsForgotten` names
no cell, so nothing says the values it dropped were not this block's. Recording
what they concern is what would settle either.


A contract with undecided allocation continuity records
`ContractAllocationRetired` for the consumed input. It removes cached cells,
initialization, and zeroed status under equal pointer forms, while leaving
definite deallocation unasserted. The edge names the allocation and its size,
so a later memory proof may cross it only for storage shown separate from that
possible release.

The call rule reads the consumed resources, and so the retired allocation, at
the call's entry: the post-call value of a pointer field the callee owned is a
fresh load, and a callee that frees `box->data` and re-points it at memory the
caller keeps would make a post-call reading retire the wrong object. A kept
owned memory fact then needs no written separation from the retired
allocation when one owned memory fact the caller lent covers the allocation's
whole byte range: the two were held at once, and owned memory is exclusive
within one valid composition. The same holds for a kept view of exactly the
bytes of a kept owned range (the view a caller holds of a descriptor a callee
returned), found by one exact lookup of that owner. Any other kept view, a
kept composite, or any kept fact when no lent owner covers the allocation
still needs a separation the path facts prove
(`caller_resource_left_stale_by_retirement` in `src/kernel/functions.rs`).

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
reallocating call added one nested allocation-size proof to relate the two.

Where the cell column names a gate, the answer is one a scope decides rather
than the edge. `extended_dag_bridging_active` and `explicit_dag_check_active`
(`src/kernel/memory_history.rs`) are scoped flags, set for the duration of
the memory-load prover and of explicit certificate validation and cleared
outside them. The wider answers are confined to those scopes because the
narrower ones are what execution pruning, load canonicalization and `close()`
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
reads only `AddressBase::proven_distinct` and the checked write set the edge
itself carries — which is path-independent, and so may be read off an interned
edge.

Two of those answers are not reachable from C yet, and fail closed where they
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

It prints the resource with the user's own names (`a[m]`, `g[0]`), names the
one step that broke the chain, and prints, in short sentences, the repair for
the case that actually applies:

| Case | What it says |
| --- | --- |
| compact recorded cell range | The read is not yet related to the recorded range contents. Establish the index/address relation or preservation needed to compare the reads. A `CellsSeeded` edge also represents input-resource materialization, so it does not identify a source store and offers no speculative index inequality. |
| one array, two indexes | ``the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`.`` |
| one array, a store wider than its element | ``the store to `a[j]` writes 8 bytes where `a` has 4-byte elements, so it covers the 2 elements from `a[j]` up and `i != j` rules out only the first of them. State `i < j`, which puts `a[i]` below every byte the store writes.`` The disequality above is not the repair here, and the *order* is: `one_element_gap_separates_bytes` gets a one-element gap from an address ladder, a bare disequality leaves the direction open so both accesses must fit in it, and a strict order fixes the direction so only the lower access must. Where neither access fits in an element there is no such order and none is offered. |
| two objects nothing separates | ``the store to `g[0]` may have written it, because `a` may point into `g`. If they are separate, require `separate(memory(a[0..1]), memory(g[0..1]))`; where the contract already transfers `g[0..1]` with `owns` or `consumes`, declaring `views a[0..1]` says the same.`` |
| a call or a loop with a write set | ``the call in between may write `g[0..1]` …`` then the same two clauses |
| the resource was written | ``the store to `a[i]` wrote it.`` |
| the read's address does not raise | ``the memory-history check could not establish that the store to `g[0]` is separate from this read.`` |
| a fact about a block | ``a fact about `a` as a whole does not carry across the store to `b[j]`.`` plus the note below |
| a model field across a call | ``` `c.rank` may have changed since function entry: the call to `bump` returned ownership of `c` with a new model, and `bump` promises nothing about this field. If it keeps the field, state `ensures c.rank == old(c.rank)` on `bump`.``` |
| a model field across a loop | ``` … the loop owns `c`, and a loop head is an arbitrary visit, so it gives `c` a fresh model. If the body keeps the field, carry it through as `invariant c.rank == old(c.rank);`.``` |
| a model field the state no longer holds | ``` `c.rank` names no model here: `c` was consumed since function entry, so this state holds no field to read. Name the value it had there, `old(c.rank)`.``` |

Every clause it proposes is one that verifies the situation it is printed for;
where none does, it says what is missing instead of naming a repair that would
not work. A whole-array fact is the case with no repair to name: the block walk
reads no stated separation at all, so the text says so rather than sending the
reader to write a `separate(..)` the walk will never consult. A model field
neither point holds is the other: `old(c.rank)` would name nothing either, so
the text says that rather than printing it.

The memory-history diagnostic uses no proof-context equality or ownership facts
and explicitly states that scope. A stopped walk does not establish that such
facts are absent. Proof reports identify the blocking store's state and both
write width and checked read range, using the same address labels and construction
legend as goals and traced facts when source names are unavailable. Subsequent
steps are described as recorded memory transitions, not C statements. The checked
read range may be
conservative when the history query has no registered load width. The stopping
point and write width are retained while the failing proof's session is active;
formatting never reruns the check in a later arena or under a different bridging
mode.

Two model-field refusals have checked repairs:
`mdtests/model_field_across_a_call_that_promises_nothing.md` /
`model_field_kept_by_a_call.md` and
`model_field_across_a_loop_without_an_invariant.md` /
`c_reads_through_a_resource_with_fields_across_a_loop.md`.
`fold_field_names_the_opened_model.md` reads the field from the captured
model of an instance the proof unfolded.

The two cases that can print both ranges offer two clauses, because two say the
same thing: a stated `separate(..)`, and — since a contract's transferred and
borrowed clauses denote disjoint memory, below — a `views` clause over the read.
The second names its condition ("where the contract already transfers
`g[0..1]`") rather than asserting it: this renderer is handed two addresses, not
the contract's clause list, and a range transferred only inside a folded
composite is not one the entry partition reaches.  Both clauses are ones the
reader can write, because `SourceCell::element_range` expresses only a
parameter or a file-scope declaration and yields nothing for a local.

An index only the lowering has a name for is printed `a[…]`, never as the
kernel variable, and no inequality is proposed over a name nobody wrote. It
does not dump memory contents. It reports the blocking step and whether later
recorded memory transitions preserve the resource.

A read or store whose address does not raise still appears
in the structured proof report as a report-local address label. Its definition and the
blocking state's construction are expanded in the shared legend.

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
| `ResourceContext::invalidate_memory_support` → `memory_derivation_affects_footprint` `src/kernel/primitives/resource_algebra.rs` | **routed** | Walks the edges between two states and drops every resource projection a step could have written. It now asks `affects` about `Resource::Ranges` for a stated footprint and `Resource::AnyMemory` for one the kernel could not name, and keeps the projection only where the answer is `Separate(Footprint(..))` — so this site is where `footprint_effect` is spent, and the only place it is. |
| `ResourceContext::entries_affected_by_memory_derivation` | another question | Chooses *candidates* from the interval index; the rule then decides. Its one obligation is to stay a superset of the steps `affects` does not answer `Separate` for — narrowing it would silently keep a stale projection. |
| `statement_call_havoc_views` `src/kernel/proof/execution.rs` | another question | Collects the call nodes between two states; asks nothing about a resource. |
| `matching_recomputed_call_havoc_views`, `memories_definitionally_equal` `src/kernel/api/contract_certification/contract_claims.rs` | another question | Matches two derivation chains edge for edge, to certify a recomputation. A whole-state equality, not a footprint. The second skips the `local:` blocks its kernel twin skips, and by the same one filter — below. The chain walk is where the two part: `transparent_base` descends past an edge that recomputation would not have minted — a store or a declaration whose block is named `local:`, a store whose value is the base's own load at that very pointer (a tactic materializing a symbolic load, which independent certification never does), and the two edges that name nothing, `ContractAllocationClaimsChanged` and `CellsForgotten`. That is a structural skip over *edges*, decided by name and by interned identity, and it is not the pointerless filter the twin spends; a `local:` name is what it reads, so an addressed local's store is stepped past here as well. Nothing is claimed about a version by descending, because the pair the descent reaches is still compared in full. |

### The eager half: a step applying its own write set

These run *at* the step, over every cell, in the producing context, before the
edge exists. Each decides the same abstract question as the matching arm of
`affects` and each decides it differently, so none is routed.

| Site | Class | Why it differs |
| --- | --- | --- |
| `call_havoc_keeps_cell` `src/kernel/primitives/memory_state.rs` | disagrees | For ordinary cells, keeps a cell when plain `ranges_proven_disjoint_from_pointer` proves the declared write set cannot reach it. A cell an owned member of what the caller keeps owning holds (`CallKeptOwnership`) is dropped from the cache too, and that member is recorded on the edge with the premises that place the cell in it, where the rule's `CallHavoc` arm reads it. A local cell whose block has a write-range base in a different form is retained only when the pointer-equality graph does not resolve that base to the cell; this catches assumed aliases while preserving direct same-block construction transitions. The rule's `CallHavoc` arm uses typed range evidence and the `_for_frame` expansion, which looks through composite definitions, so the two remain weaker in different cases. |
| `SymbolicMemory::with_call_memory_havoc`, `SymbolicMemory::matches_call_memory_havoc_result` | disagrees | The producer that applies a call's write set and the checker that re-derives what it would have written. Both now ask `call_havoc_keeps_cell`, so the retain rule is one function: the checker has to stay identical to the producer, not to the rule, and sharing the function is what makes that structural instead of remembered. Both apply it to the typed union views (`union_cells`) as well as the cells: a view is the authoritative answer to an exact typed load, and the producer used to keep every view while the checker dropped them, so a load after a call that wrote through a union member read the pre-call member (`mdtests/call_havoc_drops_a_union_member_view.md`). `click audit` accepted that proof too: a kept view is not a difference between the two states, so no coverage check asked about it. |
| `borrow_preserving_havoc_keeps_cell` | disagrees | Preserved-block membership **or** bytes `BorrowLedger::permits_memory_access` refuses a write through. An ownership question, with fail-open polarity, and no pointer-alias reasoning at all — a loop body or a joined branch arm may write through any pointer it can reach, so separation has nothing to decide. The width it asks the ledger about is the wider of the cell's value and the widest typed overlay recorded there (`union_overlay_widths`), and an unknown width fails closed. |
| `SymbolicMemory::with_loop_memory_havoc_preserving_borrows`, `SymbolicMemory::with_interface_memory_havoc_preserving_borrows` | disagrees | The loop head and the interface join, which both ask `borrow_preserving_havoc_keeps_cell`. The interface join also records a `BranchJoin` edge: the tracker can recover uncached reads by checking every incoming arm, independently of this eager retain rule. The loop head does not record that edge. |
| `SymbolicMemory::forget_zeroed_allocations_written_by` | disagrees | The other half of a call's write set: it drops the zeroed reading of every allocation the declared ranges may reach, because "reads as zero where unwritten" is a claim about contents that an unseen write invalidates exactly as it invalidates a stored cell. It drops the status for the whole allocation rather than narrowing it to a prefix, since a write set bounds where a callee may store and not where it did. The rule has no arm for it: a zeroed reading is not a resource the tracker names. |
| `SymbolicMemory::without_possible_aliasing_cells` | disagrees | A store's own eager drop, and the one site on this list that shares the rule's byte question: the address ladder is conjoined with `access_byte_overlap`, exactly as the rule's `Store` arm conjoins it, so a ladder that proves two addresses differ may stand in for byte separation only where the gap it establishes clears both accesses. Ahead of the ladder, and before `access_byte_overlap`, it asks ownership through the composition base index (`PureFactContext::access_owned_apart_from_store`, below), including the composition the store statement opens from the held folded instances whose arguments name a cached cell's base (`functions::store_opened_instance_composition`, below); a cell ownership does not place goes down the ladder unchanged. The ladder itself is `pointers_proven_distinct_for_memory_resolution`, **or** `pointers_proven_disjoint_by_explicit_range_for_memory_resolution`, **or** `pointers_directly_disjoint_by_range`, **or** `owned_composition_store_separated_evidence`. The two range rungs are the cross-base pairs offset reasoning cannot decide and the byte question answers `Unknown` for; they are a range-index scan the rule's hot `Store` arm must not pay for. The last is shared with the rule's `Store` arm and the two transport sites, and it has to be here too: a cell this function drops is lost to every later route, because the two states then differ at the read's own address. |
| `SymbolicMemory::without_field_cells` | disagrees | Same-block equality and a constant byte interval. Across blocks it removes too little, which for a copy is the safe direction; a completeness difference only. |
| `heap_allocation_may_contain_pointer`, `SymbolicMemory::freed_heap_allocation_may_contain` | disagrees | `base.block != pointer.block` answers "not contained", which is fail-open on a representation. The rule's `HeapFreed` arm is two separation ladders instead. Reaching it needs a freed allocation whose base block is not proven distinct from a live cell's block. The second is the same test over every deallocated allocation, and it is what the zeroed drop, the availability check below and contract certification all read, so the comparison by representation is at least in one place. |
| loop frame assembly `src/kernel/loops.rs`, `collect_loop_effect_check_obligations`, the multi-exit join | disagrees | Each reinstates or drops cells against the loop's *stated* effect summaries rather than a recorded edge, with a hardcoded `local:` skip. |
| `memory_diff_is_covered_by_writes`, `memory_diff_is_covered_by_ranges` `src/kernel/proof/execution.rs` | another question | The containment direction: is every observed change *inside* the declared write set. The tracker has no containment question. |

### State versus state: "do these two states agree about this read"

The tracker's `same` answers this for two points on one recorded history. These
sites answer it for two states that need no ancestry — an effect summary's
endpoints, a recomputed chain, a canonical form — so `same` cannot replace
them without losing every pair the DAG does not connect.

| Site | Class | Note |
| --- | --- | --- |
| `memory_load_is_directly_unchanged`, `memories_directly_match_for_pointer_load` `src/kernel/memory_history.rs` | disagrees | The transport rule. It already asks the tracker as one disjunct — two states that name the cell by one point hold the same cell — and the rest reads `MemoryMutatesOnly`, `MemoryEffectSummary` and `HeapAllocationFreed` over *stated* endpoints. Its per-write ladder is the same four predicates the rule's `Store` arm uses, applied to a stated write list. |
| `memories_match_for_pointer_load` `src/kernel/reasoning/memory_resolution.rs` | disagrees | Assumption-free structural agreement about one load: the same forgotten-source identity; equal sizes for every object the load may designate plus equal havoc markers; agreement about retirement tombstones and all load-observable heap lifetime, initialization and implicit-zero metadata; and equal cells and union cells under `observable_by_load`. Decides pairs with no common ancestor. |
| `memory_states_match_for_resolution`, `memory_states_proven_equal_at_pointer`, `memories_match_for_pointer_load_bounded_alias`, `memories_match_for_pointer_load_under_assumptions` `src/kernel/reasoning/memory_resolution.rs` | disagrees | The same question with assumptions: every cell the two states differ on must both miss the load's bytes and be proven distinct from the load. All refuse a load whose own block is `local:`, and all select the cells to check with `cell_is_observable_by_load`, the one filter — *not*, as they used to, by dropping every differing `local:` cell unasked. See below. The second is a thin name for the first, so that a caller asking "are these two states one state as far as this pointer is concerned" reads as that question rather than as a resolution internal. |
| `state_objects_agree`, `retirements_agree_for_load` | separation | The object half, as against the values in the cells: a size is what says an object is there and how big it is, and a tombstone is the only record that an automatic object's lifetime ended once its cells are gone. The first is the assumption-carrying comparisons' size check, and the only sizes it leaves out are the ones `local_block_no_pointer_can_reach` allows. The second is the tombstone check, which all four comparisons ask, and it allows a difference only where the load's block is proven distinct from the retired object or no pointer value in the program designates it — two exclusions, each catching what the other does not. A load through a stale alias is exactly the load these comparisons are asked about, which is why neither half may be skipped on a representation. |
| `differing_cell_bytes_miss_the_load`, `differing_cell_byte_width` | separation | The byte half, asked of each differing cell before the address ladder may speak. A cell at `p + 1` holding one byte is a different address from `p` and is still the second byte a four-byte read there returns, so an address ladder alone is not an answer. The width is read from whichever side holds a value, the wider where both do and disagree, and the widest scalar where neither does, since over-stating a width can only shrink the separated set. |
| `memory_matches_effect_summary_endpoint` | disagrees | Whether a recorded effect summary's endpoint is the state in hand: interned identity, else the assumption-free structural agreement above. An endpoint pair has no ancestry to walk, which is the whole reason this section exists. |
| `memory_load_terms_equal_for_fact_transport` | another question | Whether a fact about one load *term* is a fact about another: the two pointers proven equal, or one recorded offset equality between them, and then the state comparison. A term question that ends in a listed state comparison, not a staleness decision of its own. |
| `memory_has_materialized_load_from` | another question | Whether one state is the other with this load materialized into a cell — the cell holds exactly a load at this pointer from a state the comparison then matches. A tactic that forces a symbolic load into a concrete cell mints such a pair, so the two are one state with different cells recorded, and both the pointerless equality and the per-load comparison ask it before they compare anything. |
| `canonical_memory_for_pointer_load` | separation | A normal form, so that two states can be compared at all. Its filters are `observable_by_load` and `cell_disjoint_from_load_by_constant_offset`, one shared function each. |
| `memories_proven_equal_for_memory_resolution`, `memory_cells_definitionally_contained` | another question | Whole-state equality under assumptions, with no load pointer. The only `local:` cells and blocks either drops are the ones `local_block_no_pointer_can_reach` allows — see below. |
| `memory_range_still_available` `src/kernel/reasoning/path_facts.rs` | disagrees | Whether a memory fact established at one state still describes an available region at another: the block present in both or absent in both, the same ended-local answer, and the same freed-allocation answer for its base. A staleness question decided from two states with no path between them, and about *availability* rather than about a version — the fact may be perfectly current and still describe storage that is gone. The freed-allocation half is what separates the two states for an `ExternalArgument` allocation, whose block survives the `free`. |
| `differing_cell_pointers_possibly_aliasing` | separation | One call to `observable_by_load`. |

#### And the history has a veto over all of them

Every row above reads *state*. A cell map records what is known at a point,
and a canonical form drops what it can prove irrelevant to the load. Neither
records that a store happened, and a store into the middle of a cell drops
the cell it partly overwrote while the naming projection discards what it
leaves behind — so two states a store separates can be identical
everywhere these sites look. Absence of a differing cell is not evidence that
no store happened, and reading it as such made `*q` provably equal to
`old(q[0])` across a one-byte write into the same `int32`.

So the loads' recorded history is asked first, and it can refuse. One
memoized query, `recorded_load_history` in `src/kernel/memory_history.rs`,
answers for a pair of states and a pointer:

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
states and `load_equality_refuted_by_history` for a pair of terms, both in
`src/kernel/reasoning/memory_resolution.rs`. They reach the
`(MemoryLoad, MemoryLoad)` arm of the resolution equality, the deep
canonical-form comparison in `proves_atomic_without_search`, the origin-state
comparison in `checked_origin_load_equality`, and the bounded matcher behind
`pointer_offsets_equal_after_exact_materialization`, so one store is seen the
same way by an integer goal, a pointer-offset goal and a 64-bit goal alike.
Where a comparison holds a naming projection rather than a derived state,
`canonical_load_projection_source` leads back to the state the projection's
materialized cells were loaded from, and the pair is asked again from there.

Two things the veto deliberately does not cover, both recorded here because
they are what a later repair has to start from.

A walk that stops at a step it could not show separate has proved nothing,
so the cell comparison still speaks. That is sound only while the comparison
can see the blocking store, and it cannot when a later possibly-aliasing
store has already dropped that store's cell from both states: `a[i] = 7;
a[j] = 0; return a[m];` under `m != j` and nothing about `i` compares one
differing cell, separates it, and reads `a[m]` as unchanged. Making the stop
itself refuse is the principled repair, and it is not free: the walk's own
`Store` ladder is narrower in practice than the differing-cell scan, so a
blanket refusal withdraws field-derived and symbolic-index framing the corpus
depends on. The repair is to give the two one ladder, not to widen the veto.

Memory states the history does not connect at all keep the structural comparison.
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
| `AddressBase::proven_distinct`, `may_alias`, `observable_by_load`; `Address::blocks_proven_distinct`; `block_is_never_address_taken_local` | `src/kernel/primitives.rs` |
| `pointers_proven_distinct_for_memory_resolution`, `pointers_distinct_through_one_exact_alias`, `never_address_taken_local_versus_pointer_value`, `pointer_offsets_with_common_base_proven_distinct` and its `_distinctness_condition`, `cell_disjoint_from_load_by_constant_offset`, `cell_is_observable_by_load`, `local_block_no_pointer_can_reach` | `src/kernel/reasoning/memory_resolution.rs` |
| `range_proven_disjoint_from_pointer`, `ranges_proven_disjoint_from_pointer`, `ranges_directly_disjoint_from_pointer`, `pointers_directly_disjoint_by_range`, `pointers_proven_disjoint_by_explicit_range_for_memory_resolution`, `pointers_proven_disjoint_by_shallow_explicit_range` | `src/kernel/assumptions/memory_reasoning.rs` |
| `typed_store_separated_ranges_evidence`, `typed_range_disjoint_from_pointer_evidence`, `typed_ranges_disjoint_from_pointer_evidence`, `heap_allocation_proven_separate_from_pointer`, `owned_composition_store_separated_evidence` | `src/kernel/memory_history.rs` |
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
arm, `SymbolicMemory::without_possible_aliasing_cells` and the state comparisons
all conjoin it, which is what keeps one store from being separate at one site
and overlapping at the next.

Overlapping is also not *supplying*. A walk that stops at a store because the
store writes bytes the read returns has learned that the cell changed, not what
it now holds: a one-byte store of `7` inside a four-byte read is one of that
read's bytes, and a four-byte store around a one-byte read holds three bytes
the read does not return. The routes that read a value off the history —
`resolve_load_along_memory_derivations`, the stored-value arms of
`explicit_atomic_equality_from_memory_derivations` and of the load-equality
walks, the pointer-offset resolution, and the stored-origin load equality —
take a store's value only through `write_supplies_read`
(`src/kernel/resource_tracker/cell_source.rs`): the store starts at the read's
address and is exactly as wide. Click has no rule that extracts a narrower read
from a wider store or assembles a wider read from narrower ones, so any other
overlapping store stops the walk at the state it produced, which is what the
read is then known to read (`mdtests/a_byte_store_is_not_the_value_of_the_wide_read_it_lands_in.md`).
The walk itself is asked about the access width recorded at the read's address,
and a width nobody recorded is the widest scalar, which no narrower store
supplies. Whether the store or a cell the stopping state materialized is the
read's *value* is the read's kind's question, below.

#### A load term carries its read's kind

A load term is a value, and what a read returns depends on more than its
address: a byte of `0xFF` is `-1` read as `int8` and `255` read as `uint8`, and
an `int32` read at the same address returns all four bytes. A
`MachineTerm::MemoryLoad` therefore carries a `LoadKind`
(`src/kernel/primitives.rs`) beside its state and address: `UInt8`,
`Int16`, `UInt16`, `Int32`, `UInt32`, `Bits64`, `Float32` or `Float64`.
Four- and eight-byte integer reads keep their bit pattern in the term;
two-byte reads hold the extended value, which signedness changes. A 32-bit
read keeps its signedness in its kind and is its own load, and both 32-bit
kinds read one word (`LoadKind::reads_word_of`, `LoadKind::is_word32`): the
equality graph relates the two reads of one cell by σ (R-mem), and a route
that answers a load term from a cell reads the stored word whichever
signedness stored it, while a typed read of the other signedness returns
the sign cast σ of it (rule K5,
[mathematical integers](mathematical-integers.md#the-32-bit-sign-cast)).
Eight-byte reads are one kind, `Bits64`, and let the `ProgramValue` wrapper choose
signed or unsigned. A value of an algebraic type held in memory
(`AlgebraicTermNode::MemoryLoad`) is no integer read: walkers and load-atom
comparisons reach it through a stand-in decoded at its own type,
`LoadKind::Algebraic(T)` (`AlgebraicTermNode::memory_load_carrier`), which
equals no C scalar read of its cell. A pointer read is an `Int32` read, because Click names a
pointer value by the four-byte word at its address, as a materialized
pointer field's cells hold it.

**One byte, one name.** A byte has a single load term: its unsigned (`UInt8`)
read. A signed (`Int8`) read of the byte is not a load term of its own; it is
the two's-complement conversion of that one term,
the generic `Cast { UInt8 -> Int8 }`, built only by
`MachineTerm::memory_read` (and `canonical_form_of_load`, which delegates
to it for the `Int8` kind). So a signed and an unsigned read of the same byte
are related by construction: `s[i] == -1` names the same unknown as
`u[i] == 255`. A `MemoryLoad` of kind `Int8` is never formed; the load
registry refuses to name one (`load_variable_for_term`), so a producer that
bypassed `memory_read` gets no name and no fact rather than a second, unrelated
value of the byte. A cell stored with the other signedness is read the same
way (`ProgramType::read_cell`, `LoadKind::read_cell`): C11 6.5p7 lets any character
type read an object's bytes, and the reinterpretation is the same modular
conversion.

**A load term's identity is its load and its kind** (`design/loads.md`, step
3a). `MachineTerm::MemoryLoad(point, cell, kind)` holds a `ReadPoint`, the
point its producer selected, and a `LoadCell`, the address as the producer
spelled it together with its interned `Load` (`src/kernel/primitives/load.rs`),
keyed by the point's read key and the cell. Equality and hashing compare the
load's id and the kind, and ordering compares the load by content (its stored
content hash, then point and cell) and then the kind, so iteration order does
not depend on interning order: the `ReadPoint` compares equal to every
other, and the address is not compared, since the load's identity holds it.
Within one memory arena this is the equivalence the term had when it compared
point, address and kind, because `ProgramPoint` equality is read-key equality
there; across arenas two memory-named reads of equal-content memories are two
terms. A new arena starts only with a new verification session, which also
clears the load interner, so such terms never meet in one proof
(`design/loads.md`, step 3a-i).
Two reads of one cell at one read key are one term whichever selection (exact,
indexed write, indexed cell) built each, and each keeps its own selection:
consumers branch on the term's `ReadPoint`, never on `Load::point`, which is the
first selection of that key. Reads of one cell at two kinds share the load and
are two terms. `MachineTerm::read_named` is the only builder, through
`read_operands`; a substitution or rewrite that changes the address builds a
new read and so interns the load of the new cell
(`build_support/read_construction.rs`). Because the fields compare as a whole
term, compare `point.point()` or `cell.address()` when code means the
producer's point or address alone: `ReadPoint == ReadPoint` is always true and
`LoadCell == LoadCell` compares loads.

When a pointer read reuses a cached scalar load name, its coordinates come from
that name's defining read. Reading the same cached cell through an
alias in a different symbolic storage block must not rebase its pointer value
onto that alias. The address lookup still checks the alias and read authority;
recovering the defining coordinates grants neither. The loop-cursor fixtures
`loop_cursor_pointer_read_preserves_child_model.md` and
`loop_cursor_pointer_read_requires_owner_alias.md` cover both sides, and
`cached_pointer_value_keeps_its_defining_coordinates_and_scales` checks that the
conversion does not scan unrelated aliases.

Before the kind was part of the term, two reads of one address in one state
were one term whatever they read, and every route that equates loads equated
them: `s[i] == u[i]` through a `signed char*` and an `unsigned char*` view, and
`q[i] == u[4 * i]` for an `int32` and its low byte, were provable, in a body, in
a contract, across a call and through `at(...)`. With one name per byte the
signed read is now the conversion of the unsigned one, so `s[i] == u[i]` is
still refused (the two differ for every byte of `0x80` or more) while
`u[i] == 255` proves `s[i] == -1` and `s[i] == -1` proves `u[i] == 255`
(`mdtests/a_signed_and_an_unsigned_byte_read_are_two_values.md` and its
neighbours; the backward rule is described in
[byte representation](byte-representation.md#character-reads-of-one-byte-cells)). The load variable is named by the term, so its identity, its
registry entry (`registered_load_kind_for_variable`) and its defining equation
carry the kind too.

The kind is checked in three kinds of place:

- every route that equates two load terms compares their kinds along with
  their addresses — the history walks (`LoadCellWalks`, keyed and memoized by
  kind), the origin, call-event and stored-value equalities, the
  load-address congruence (`load_address_congruence_evidence`), the
  pointer-load signature in the equality graph, and the state comparisons
  that transport a load between states;
- every route that answers a load term from a value — a store the walk stopped
  at, a cell a state holds (`MemoryDagCell::resolved_value`,
  `resolve_memory_load_value`, the deep canonical form, exact-load
  normalization, `memory_materializes_atomic_load`) — asks
  `LoadKind::reads_value`, or `LoadKind::read_cell` where a read of a cell
  of the same width and the other signedness answers with the same bits
  converted (σ of the stored word at 32 bits): the value is exactly what a
  read of this kind returns;
- the int32 equality graph takes a load variable as an int32 load only when its
  kind is `Int32`, which every 32-bit load variable's is. Its recorded width is the widest access seen at the
  address, so a byte read beside an `int32` read used to qualify
  (`mdtests/a_byte_read_is_not_the_int32_read_at_its_address.md`).

A refusal whose two sides are reads of one address of different kinds says so
(`describe_load_kind_mismatch`), rather than naming a store in between that is
not the cause.

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
  aggregate a call returns by value, carries `AddressBase::Temporary`. It is
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
through the index of assumed `AddressEqual` facts to a non-symbolic form and
asks the same question there
(`pointers_distinct_through_one_exact_alias`). `ensures result == &g[0]` and
`ensures result == p` are what that reads, and
`stored_value_at_equal_pointer` — which used to search only the load's own block
for a stored cell, and so answered "no stored value" for exactly those reads —
now filters by `observable_by_load` instead of by block name. A stated
*disjunction* of equalities needs no rule of its own: `close()` splits it and each
case holds its exact equality
(`mdtests/proof_branch_pointer_local.md`). The hop is substitution of equals,
so it is also what keeps the attack refused: resolving a returned `&x` moves the
read to `x`, which is not distinct from a store to `x`
(`mdtests/returned_pointer_to_a_caller_local_may_alias_it.md`).

##### The same shortcut, written on the other side

Withdrawing the exception from `observable_by_load` did not withdraw it
everywhere, because one filter of the same shape was written out by hand.
The three assumption-carrying state comparisons —
`memory_states_match_for_resolution`,
`memories_match_for_pointer_load_bounded_alias` and
`memories_match_for_pointer_load_under_assumptions` — check the cells two
states differ on against the load, and each selected those cells with
`!cell.block.starts_with("local:")`. A differing `local:` cell was therefore
dropped before anything was asked about it.

That is the withdrawn exception with the sides swapped: instead of claiming an
unresolved load reads only its own block, it claims no local is a block such a
load reads. `&x` passed to a callee and returned is the counterexample in both
directions, and
`mdtests/an_unresolved_pointer_sees_the_store_to_a_local.md` is the false
theorem the second form admitted — the same C as the mdtest above with the
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
object map — each block's size, and the tombstones that say an automatic
object's lifetime has ended — and it carried the shortcut in its own form:
the three assumption-carrying comparisons compared the size of every block
*not* named `local:`, and none of the four compared the tombstones at all. An
size is what says an object is there and how big it is, and a tombstone is
the only record left once the object's cells are gone, so two states
disagreeing about either disagree about what a load through a pointer that may
designate it reads. The size check is now `state_objects_agree`, dropping
only what `local_block_no_pointer_can_reach` allows, which is the same thing
the pointerless equality below spends; the tombstone check is
`retirements_agree_for_load`, which all four ask, and which allows a difference
only where the load's block is proven distinct from the retired object or no
pointer value designates that object at all.

##### And the same shortcut with no pointer at all

Two neighbours carried it a third time, and neither had a load pointer to ask
`observable_by_load` about: `memories_proven_equal_for_memory_resolution` and
its certification twin `memories_definitionally_equal`, whole-state
equalities that each dropped every `local:` cell and block before comparing.

The one caller that decided a *load* question with them, the memory-resolution
order walk, had a pointer and passed it to
`memory_states_proven_equal_at_pointer`. That walk has since been removed:
memory resolution reads order from the difference graph, which compares no
states.

What is left is genuinely pointerless. The remaining callers of
`memories_definitionally_equal` — the effect-chain endpoint checks in
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
filter's: a scalar local's program-visible value is in the `LocalEnvironment`
binding, which these callers either compare exactly as part of `ExecutionState`
equality or do not ask about, and a caller that needs the slot cell compares
`ExecutionState::local_cell_values` beside the memory, as
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
`a_pointerless_state_equality_drops_only_a_local_no_pointer_can_reach`
(`src/kernel/tests/memory_reasoning_tests.rs`), where a state pair differing
in an address-taken local is not equal — for the pointerless comparison, for
its certification twin, and for a symbolic-pointer load — while a pair
differing only in a local no pointer can reach is.

One relative of these two is deliberately wider and stays so:
`program_effect_memories_definitionally_equal` strips *every* local from both sides
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
that Click refuses on every displaced access (`MemoryCanStore` /
`access_in_bounds`), and an integer cast to a pointer is outside supported C. An `&x`
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

Imported functions use the same pass over their lowered typed bodies, including
generated scalar call-result locals. The walk checks every declaration and
address-forming expression; aggregate and array names remain addressable. A
non-null pointer literal in a lowered body makes the whole bundle conservative,
because it can name storage without a source address expression. This is source
analysis performed once before verification, not a new separation assumption
attached to an arbitrary symbolic destination.

Two things follow from where the answer is kept.

- It is a set of **names**, program-wide. A `local:` block says nothing about
  which function declared it — `local:x` in `f` and in `g` are one name —
  while the resolution memo and the canonical-projection cache are scoped per
  verification, not per function. A per-function answer would be cached under
  whichever function asked first and served to the next.
  `mdtests/a_local_addressed_in_another_function_is_framed_by_ownership.md`
  is what that costs: one `&guard` anywhere removes every `guard` from these
  walks, and only a held composition's ownership still frames it.
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

`memory_history::owned_composition_store_separated_evidence` is the rule:
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
  expressed with pointer terms whose loads carry their own state. A store
  cannot move the bytes a range named, and consuming, transferring or freeing
  a resource cannot make two ranges that were disjoint coincide. So a
  composition recorded at an earlier program point is as true later as it was
  then — which is why the rule does not need the resource to still be held,
  and why the retained hop names the composition as its premise all the same.
- **Facts only, never a name.** Composition facts are path facts. The rule is
  spent exactly where a typed `separate(..)` is spent — the fact-consulting
  route — and the two naming walks cannot reach it, because both are handed
  `PureFactContext::new()` (`resource_tracker::cell_source_for_naming` and the
  block-version walk) and an empty composition set decides nothing. On the
  querying route the answer is re-derived per query, keyed by the context
  (`resolution_query_memo_id`), and never written onto an interned edge.

It sits **last**, after every cheaper check, at the four places the
store-versus-load question is asked: the tracker's `Store` arm, the two
transport sites in `memory_history` (`memories_directly_match_for_pointer_load`
and the `MemoryMutatesOnly` arm of `memory_load_is_directly_unchanged`), and
`SymbolicMemory::without_possible_aliasing_cells`. The last of those is the one that
decides `c_contract_executes_acquire`, and it is not optional: once a store has
dropped a cell, the two states differ *at the read's own address*, and no
later framing route can recover it. It is kept beside
`pointers_directly_disjoint_by_range`, which is at that site for the same
reason, and it does **not** expand recorded composites. Call and loop frame
queries likewise use the ordinary indexed range/pointer separation route;
there is no whole-composition expansion fallback.

Cost: an emptiness gate first, then two block-bucket lookups per composition
held, no pair materialization and no expansion.

At a store the compositions held are the writer's current ownership only.
The write path states the observable composition of the state's resources,
and any composition `store_opened_instance_composition` opens, as the
context's store owners (`PureFactContext::with_store_owner` and
`with_additional_store_owner`), and the rule and `owned_store_footprint`
read those alone in a context that has them
(`PureFactContext::store_compositions`). A composition stated at an earlier
point stays true and stays a path fact, but a store reading every one would
cost work in the length of the path at every store (`roadmap/scaling.md`).
`store_separation_work_is_independent_of_earlier_compositions`
(`src/scaling_tests/kernel/tests/memory_reasoning_tests.rs`) is the
regression and `store_separation_reads_the_store_owners_and_not_earlier_compositions`
(`src/kernel/tests/memory_reasoning_tests.rs`) the attack set.

Where no writer stated owners, as in the loads an `unfold` or a call
resolves, the rule and the same-block separation search
(`PureFactContext::composition_separated_members`) read only the
compositions listed under the two objects' member bases and blocks
(`CompositionMemberIndex`, `src/kernel/primitives/composition_member_index.rs`).
A composition is listed only under the owned members it holds beyond an
earlier admitted one, its predecessor: the last state of its storage
origin, or else the last admitted composition or the first when their member
indexes share structure; the first composition admitted is unlisted and read
by every question. Admission costs what changed, and the module comment
proves that a pair held by any stated composition reaches one through the
listings under the pair's keys.
`store_separation_without_an_owner_reads_only_listed_compositions`
(`src/scaling_tests/kernel/tests/memory_reasoning_tests.rs`) is the
regression.

A store through a `Symbolic` pointer asks only the cells a pointer value can
reach. Every block admits a `Symbolic` address, so its `AliasCandidates`
narrow nothing, but no pointer value designates the slot of a local whose
address is never taken (`never_address_taken_local_versus_pointer_value`).
The cell store keeps the keys of every other concrete cell
(`CellStore::pointer_reachable_cells`), caught up by diffing the concrete map
since its lineage last asked, and the store visits those alone, unless a
stated exact equality places the pointer in such a local.
`a_symbolic_store_skips_locals_whose_address_is_never_taken`
(`src/scaling_tests/kernel/tests/memory_scaling_tests.rs`) is the regression.

A load through a `Symbolic` or `AddressBase::Load` pointer reads the same map,
which holds each reachable cell's value as well as its key
(`CellStore::caught_up_pointer_reachable`). Such a load observes every
reachable cell except, for a loaded pointer, locals declared after it was
read, and cells of its own block at a disjoint constant offset, so
`canonical_memory_for_pointer_load` starts from the shared map and asks its
filters only about the `local:` cells and the load's own block
(`CellStore::retain_for_unresolved_load`); the check for a common
materialization source and `source_holds_cells_observable_by` walk the map
too, so no slot a pointer cannot reach is visited. Without it, the
projection rebuilt the cells of every other object at every such load.
`unresolved_load_projection_ignores_earlier_objects_and_hidden_slots`
(`src/scaling_tests/kernel/reasoning/memory_resolution.rs`) is the regression.

`SymbolicMemory::without_possible_aliasing_cells` also asks the same law *first*, in
an indexed form. Every pointer parameter shares the one `ExternalArgument`
block, so neither `AliasCandidates` nor the block-pair separation index
narrows a store through one parameter, and every cached cell of every other
parameter reaches the ladder, where the range rungs fail slowly: each failing
search asks every owned member of the composition whether it holds the
access. So the store computes once which owned members hold its
written bytes (`PureFactContext::owned_store_footprint`), and each cached cell
then asks whether a *different* member of one of those compositions holds all
of its bytes (`access_owned_apart_from_store`). Both lookups go through each
composition's `memory_by_base` index under the additive base forms of the
address (`p`, `p + f`, `p + i·w` and their left spines), never a block
bucket, and membership is the structural route only — base, or base plus
one displacement — with the two endpoint bounds proved; the whole access must
fit, not just its first element. The guards are the ones above: the two
addresses must not be proven equal, and ranges whose base forms were
later proven equal must not overlap. A cell the rung does not place goes
down the ladder unchanged, so a miss costs time and never a decision.
`a_store_beside_owned_parameter_fields_is_linear_in_the_cached_cells`
(`src/scaling_tests/kernel/tests/memory_scaling_tests.rs`) is the regression: 96, 160,
288, 544 units at 4, 8, 16, 32 cached parameter fields, where the ladder
alone charged 376, 1508, 8732, 60940.
`a_store_through_one_parameter_forgets_another_unless_ownership_separates_them`
and `a_cell_straddling_two_owned_members_is_not_separated_from_either`
(`src/kernel/tests/memory_reasoning_tests.rs`) are its attack set.
`stores_beside_many_owned_ranges_scale_near_linearly`
(`src/scaling_tests/surface/tests/scaling_tests.rs`) is the deterministic regression: the
query's own work over 2/4/8/16 stores is 9, 11, 15, 23 units.
A cell a held *folded* instance owns is framed the same way, one body layer
down. Compositions do not open folded instances, so before the store frames
its cached cells, `functions::store_opened_instance_composition` asks which
owned instances of the state's *current* context have a pointer argument
naming an additive base form of a cached cell the store could drop
(`owned_instances_by_pointer_argument`, an index maintained as instances
enter and leave the context), opens each such instance whose body is
unconditional, unmatched and witness-free one layer at the current state
with its own fields, exactly as `unfold` and the call's kept-by-caller rule
open it, and forms one composition of the owned member holding the written
bytes and the opened bodies' owned ranges. The current context is a valid
composition held here and an instance owns exactly what its body owns, so
those ranges are disjoint from the written member; like every composition
fact the claim is about addresses, so it stays true after the store. The
store assumes that composition before framing, where both the ownership-first
rung and the ladder's composition rung read it, and records it as a path
fact, so the rule's `Store` arm and the two transport sites read the same
members later. Only instances held now are opened, never one a recorded
composition names: a body read at a state where it is no longer held could
name someone else's memory. The composition must pass the validity check a
flat context of the same ranges would, so a path whose facts prove an opened
range overlaps the written member (`requires s == other` beside a folded
instance owning `*s` and a flat `*other`, which no caller can
lend) opens nothing. A matched, guarded or witness-bearing body, a nested
instance, an iterated clause and a view contribute nothing. The unmatched
body's cells are named at contract entry, as a selected arm's are, so there
is a cached cell to keep (`docs/internals/canonicalization.md`). Cost: a
constant-time gate on the argument index, then one argument-index lookup per
form of each cached candidate cell and one body evaluation per instance
named; `a_store_opens_no_folded_instance_whose_arguments_name_no_cached_cell`
(`src/scaling_tests/kernel/tests/resource_scaling_tests.rs`) charges 55 units at 16, 64, 256
and 1024 unrelated instances (heap-block instances and parameter instances
with no cached cell), and
`a_store_opens_folded_instances_in_work_linear_in_the_aliasing_ones` 272,
520, 1016, 2008 at 8, 16, 32, 64 aliasing ones
(`mdtests/a_store_keeps_a_cell_a_folded_instance_owns.md`; negative
`mdtests/a_store_through_an_equal_descriptor_forgets_a_folded_instance_cell.md`).
`a_composition_separates_a_store_from_a_load_only_through_two_owners`
(`src/kernel/tests/memory_reasoning_tests.rs`) is the attack set — an owner
beside a view, a cell past the end of every member, a folded composite whose
body would cover the cell, a single member asked to separate an address from
itself, and a retained hop offered to a context that no longer holds its
composition.

##### The entry partition

The composition rule above must *not* be widened to cover
`mdtests/const_callback_field.md`. `read_view(struct reader *r, const int *p)`
holds `owns *r` and `views p[0..1]`, both written in one `external`
block with symbolic offsets, and its claim is true: a caller cannot both
transfer `*r` and lend a window inside it, because suspending the write
authority for the borrow leaves no usable copy to transfer
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
| a call through a function pointer or a `contract` interface | the same funnel, from `execute_program_function_call_paths` and the contract-transition sites | the same planner |
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

- `split(g, g)` from a caller holding `owns g[0..4]` — refused, *"cannot prepare the call's
  borrow for `owns g[0..1]`. A required resource overlaps a live borrow."*;
- the same through a function pointer under `contract Split` — refused
  identically;
- `split(g, q)` where the caller holds `owns g[0..4]` and nothing about `q` —
  refused, *"cannot supply `views q[0..1]` at this call. The caller needs an owner or
  a live view that covers it."*;
- `split(g, q)` where the caller also holds `views q[0..1]` — accepted, which
  is the induction step: the callee's pair is a reborrow of the caller's own
  pair.

###### Where the fact lives

It needed no new fact kind and no new framing route. At contract entry, each
(transferred memory clause, borrowed `views` clause) pair of one contract
yields the ordinary explicit separation `separate(memory(X), memory(Y))` —
`Proposition::ResourceSeparate` over two `Resource::Memory` operands, exactly
what a written `requires separate(memory(a[0..n]), memory(g[0..1]))` lowers to
(`mdtests/a_separated_array_argument_survives_a_global_store.md`). The Store
ladder therefore spends it at `typed_store_separated_ranges_evidence`, where it
spends a stated one, and the havoc side reads it at
`typed_range_disjoint_from_pointer_evidence`.

Range membership can retain one address form at a constant byte displacement
from the selected base, supplied by the maintained pointer-equality graph.
This handles a post-call pointer connected to a model
identity through another alias. The checker requires full pointer equality in
the current context and checks the first and last addressed elements against
the selected range; equality alone grants neither membership nor separation.
It does not enumerate aliases or recover older memory. A context without a
required alias or separation, or either access extended beyond its range, does
not check the store witness. The named-root-call fixture and
`graph_aliased_range_membership_checks_complete_access_and_scales` cover this
case, including unrelated aliases and partial coverage. This fallback follows
the direct and exact-alias checks. It reads the affine class coordinates without
expanding producer expressions or retrying symbolic bounds; the arena-frame
failure fixture pins the ordinary refusal below its existing work budget.

`functions::contract_entry_partition_facts` is the rule, and it reads the
contract's evaluated **clause list** — the `Vec<CheckedResourceFact>` that
`evaluate_function_resource_context_with_metadata` returns, one fact per
written clause — never a context. That is the whole discriminator: a context
holds the owner observation above, and the clause list does not.

The resulting separation remains path evidence, not a permanent address fact.
A later equality can make its two ranges overlap while the original
`ResourceSeparate` proposition remains in the context. Before an indexed
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
  and a second statement of one rule is a second place a fix has to find;
- **a clause that is not plain memory.** A composite's owned footprint is its
  expansion, and `separate(memory(..), memory(..))` cannot name it without
  expanding it, so the pair is skipped outright rather than approximated.
  `owns *r` is *not* such a clause: `*r` lowers to the plain
  range `r[0..size/4]`, which is what makes `const_callback_field` expressible.

The entry-clause generator still does not expand composites. Once a proof
explicitly opens them, separation can instead follow checked borrow bindings:
an exposed memory view carrying a live occurrence-bound borrow is separate from
a separately held memory owner in the same validated composition. Ordinary
observations of an owner carry no borrow binding and cannot use this rule; two
borrowed views cannot use it either. Rewriting or removing a view must preserve
its exact checked occurrence, not just its printed resource term.

Address-indexed composition sources feed the shared separation query used by
read normalization, resource goals, and memory evidence. A retained memory hop
rechecks the source composition, both range memberships, and the current
non-overlap guards. A later equality proving overlap invalidates that hop.
No pairwise facts or recursive footprint expansion are produced.

The two sites that know they are at a contract entry produce it independently
from the same list, so neither trusts the other: the body proof's
`initial_claim_context_with_caller_owner` (`src/surface/proof.rs`), and
`contract_certification::program_function_contract_entry_facts`, which records the
partition as an entry fact with origin `Partition`, beside the other facts it
derives from the contract's own clauses and the resources those clauses
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
sides representing one fact identically, and it can only make that check refuse
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
`pointer_params_separate_by_transfer_and_borrow.md` is the two-parameter one.

Loop `owns`/`views` clauses are **not** part of this. A loop head is not a
contract entry: there is no call-site planner between an iteration and the
next, so the induction above does not run, and a loop's clause list gets no
partition facts of its own. A function's entry facts reach its loops the way
every other entry fact does, as path facts of the context the loop starts from.

The borrow family — `BorrowLedger::permits_memory_access`,
`protected_range_proven_overlapping`, `active_memory_overlaps` — is **not** in
the entry table above. It is fail-open by design and its soundness rests on the
ownership partition rather than on the predicate (`src/kernel/borrows.rs`), so it
must never be merged with the fail-closed families there.

### Sites that only look like this question

`may_refer_to_memory_block` (resource selection before
`is_proven_separate_from_allocation`), the `held_child_witness` block filter
(witness naming for a `fold`), `is_external_memory_pointer` (evaluation
classification), the `local:` authority gates in `src/kernel/api.rs` and
`src/kernel/functions.rs`, `is_preexisting_write_pointer`, and the block
comparisons in `src/surface/diagnostics.rs` all compare block identities
without deciding staleness. Two carry a residual risk worth naming:
`may_refer_to_memory_block` compares a block by representation before the
proof-based allocation-separation check runs, so a caller resource represented
differently from a retired allocation is skipped rather than refused (the call rule draws the
same selection from the resource indexes, through
`ResourceContext::facts_that_may_refer_to_memory_block`, so its cost is the
retired block's candidates and not the caller's whole frame); and the
`held_child_witness` filter accepts `own.block != pointer.block` as "a
different pointer" with no proof, which selects a witness rather than proving
anything.

## Quantified frames are checked facts, not names

A read's name must be the same in every proof context, so the naming walks
read no facts; this holds for a function's entry facts too. Entry separation
does not make it true: pointer parameters share one `ExternalArgument` block,
and `separate(memory(left[0..n]), memory(visited[0..n]))` says nothing about
`left[k]` outside `0..n`. With `visited == left + n` the contract holds and
`visited[cur] = 1` writes `left[n + cur]`, so naming `left[k]` after the
store by its entry version would be sound only for some `k`, and naming the
whole `int32[]` argument `left` by its entry state would be false outright
(a pure function may read `left[n]`). A frame therefore stays a checked fact
about the reads a guard admits.

`src/kernel/quantified_frame.rs` is that fact. An explicit `transport(P, Q)`
whose single-fact route refuses walks `P` and `Q` in parallel: each universal
binder is renamed to a fresh identity, the target's guard is assumed on the
proving side (an implication's antecedent is proved in the opposite
direction), and each differing condition leaf is carried by the kernel's
checked load-history question (`explicit_atomic_equality_from_memory_derivations`
and the condition bridge's `memory_loads_proven_equal`), read in the querying
context's own facts rather than only the listed ones, or by the ordinary
single-fact transport, read in its own listed and certified premises. A
differing `defined(..)` leaf is carried by that single-fact transport, which
preserves initialization and lifetime evidence. A source conjunction meets a target
that is not one by conjunction elimination, so `memset`'s
`defined(dst[k]) and dst[k] == v` carries its value conjunct alone. So `forall (k) { 0 <= k and k < n and k != cur implies
at(before, visited[k]) == visited[k] }` crosses the store to `visited[cur]`,
and `forall (k) { 0 <= k and k < n implies old(left[k]) == left[k] }` crosses
it and a call whose checked write set is `visited[0..n]`. Every per-read
decision is the store, call and history rule above; the frame adds only which
facts a leaf may read, and like the fold read frame its answer enters no name
and no assumption-free cache. A source that is a reflexive equality under
binders and guards needs no proof, and `close()` offers `at(label, x) == x` its
reflexive source as it already offered `old(x) == x`.

The attacks are the `mdtests/quantified_frame_rejects_*.md` family: a guard
that admits the written cell, a guard past a stated separation, a read past
a separated range (the `visited == left + n` witness), an eight-byte store
beside the excluded element, an unseparated alias, a global that may be the
array, a call and a recursive call writing the range, a parameter
reassigned before the store, both state orders, a second store the guard
admits, a guard whose own read the store widens, a loop havoc and a release
by `free`. Each is refused with the leaf it
had and the leaf it wanted.

## Iterated guarded ownership

This section is the design record for the resource-body clause

```text
forall (k: int32) where lo <= k and k < hi {
    if g[k] == v { owns base[s * k + a..s * k + b]; }
}
```

and the kernel fact it lowers to. It belongs here because the one hard
question about it is a version question: the guard is read against the
*current* guard cells, so the fact's meaning changes whenever those cells do,
and the kernel has to know exactly which transitions may change them.

### The fact

`Resource::Iterated(IteratedMemory)` (`src/kernel/primitives/iterated.rs`)
carries the element base and width, the constant stride and offsets, the two
index bounds, the guard (cell base, cell type, `==` or `!=`, compared value),
and a short list of *holes*: indices about which the fact currently makes no
claim. Its denotation in memory `M` is the separating conjunction, over every
`k` in `lo..hi` that is not a hole, of `base[s * k + a..s * k + b]` when
`g[k] OP v` holds in `M` and of nothing otherwise. The name of the declaring
resource travels with the fact for diagnostics and takes no part in its
identity, so two definitions that declare the same clause over the same cells
denote one holding.

The family is exact-match (`IteratedResourceAlgebra`): two facts are the same
when every term is equal or proved equal, holes in order. It never splits or
joins, and it grants no access — a load or store needs an element taken out
as ordinary memory, so no memory authority check ever reads the fact.

### The invariant

At every fold of the declaring resource the fact has no holes, so it holds
exactly the elements whose guard is true. While the resource is folded its
guard cells are inside it (validation requires the body to own every guard
cell it reads), so nobody can write them and the fact unfolds meaning what it
meant when it was folded.

While the fact is unfolded, every operation preserves its denotation:

- Indexed `unfold` requires the index in range, its guard known true, and the index
  provably different from every hole; it adds the index as a hole and
  composes the element as owned memory. Before, the fact held the element;
  after, the element is held outright and the fact claims nothing there.
- Indexed `fold` requires a hole at the index and its guard known true, consumes the
  element, and removes the hole.
- Whole-clause `fold` and `unfold` require every guard decided one way by a quantified
  fact, which the kernel instantiates once at a reserved arbitrary index under
  the range hypotheses. With every guard true the fact is the covering range;
  with every guard false it is empty. Whole-clause `fold` also requires the guard cells
  to be owned, so the formed fact is as stable as a declared one. The guard
  cell at the arbitrary index is read as a C load; a never-written heap cell
  has no value until a fact establishes one, so when that read fails the
  quantified fact is first instantiated at the cell's load and the cell read
  again under the result. The second read still decides initialization; this
  is what lets an initializer form the clause over a map it has just allocated and
  zeroed in a loop (`mdtests/iterated_ownership_fold_fresh_heap_map.md`).

### The guard-store rule

A C store to a guard cell at index `j` is permitted exactly when the fact
claims nothing at `j` before the store: `j` is out of range, `j` is a hole,
the guard at `j` is known false, or the element at `j` is owned outright in
the same context. The last case needs no guard fact: a valid resource context
is a partition, so a context that owns the element cannot also hold it inside
the fact, and the fact therefore claims nothing at `j` whatever the cell
says. That is what lets the free protocol clear a flag with no fact about it.

`plan_iterated_guard_store` (`src/kernel/iterated.rs`) runs in the statement
evaluator before the write. It makes `j` a hole for the write itself — so the
write provably changes nothing the fact claims — and afterwards removes the
hole when `j` is out of range or the stored value makes the guard known false,
since excluding an index and including it with a false guard denote the same
thing. A store that makes the guard true leaves the hole open; the element
must be restored with indexed `fold` before folding the whole resource. Any other store is
refused: at an index whose guard is true and whose element was not taken out,
the fact would silently gain or lose a cell.

Soundness rests on every write to the guard cells being one of these
permitted stores or a transition that drops the fact:

- The statement evaluator is the C store path, and it calls the planner. The
  memory transition it then makes is marked as checked
  (`ExecutionState::set_memory_with_checked_stores`).
- Every other memory transition goes through `ExecutionState::set_memory`, whose
  `invalidate_iterated_facts` walks the derivation steps between the two
  states, visiting only the facts filed under each written block. An
  unchecked store keeps a fact only when it provably misses the guard block
  or names a hole structurally; a call's havoc that may write the guard
  cells, a free, and an ended lifetime drop it. Dropping loses ownership,
  which is sound; keeping a claim that may have changed is not. Memory states
  are interned by content with first-wins histories, so the later state
  can carry the history of an earlier, content-equal one that never passed
  through the earlier state of this transition. The walk therefore steps
  both states back to their nearest common ancestor (arena ids strictly
  decrease along a derivation) and skips a store that leaves its cell with
  the same value in both; walking the later state alone visited unrelated
  stores to object fields and dropped the fact
  (`mdtests/iterated_ownership_run_scan_crosses_its_locals_ending.md`).
- A loop-head havoc keeps the fact. The head is a generalization, not a
  write: a loop that inherits the fact runs every body store through the
  planner, and its back edge compares the fact like any other resource. A
  loop that declares its own resources executes its body without the frame's
  facts, so no body store meets the planner; the loop rule drops from the
  frame any fact whose guard cells the loop may write
  (`frame_out_iterated_facts_written_by_loop`).
- `free` refuses while a fact refers to the freed block, because the fact is
  indexed under both of its blocks and `facts_that_may_refer_to_memory_block`
  reads that index.
- A loop that declares a resource, and a call whose contract owns one,
  havoc the memory those resources own. That footprint
  (`checked_owned_memory_ranges`, `OwnedFootprintDerivation` in
  `src/kernel/functions.rs`) is derived from the resource definitions, not
  by opening the held resources as `unfold` would: each owned clause of each
  body, with the parameters bound to the arguments and an instance's fields
  where they are known, evaluated at the loop or call entry, and the same
  for every contained composite and named child, whose arguments are
  evaluated there too. An iterated fact counts as the span of every element
  it could hold, whatever its guards and holes say. A matched body whose arm
  is not decided contributes the union of its arms, a guarded body whose
  guard is not decided counts as active, and a composite's witness is bound
  as `unfold` binds it. The descent follows definitions, so it terminates
  without a nesting bound and costs one visit per family on a chain
  (`a_layered_footprint_is_linear_in_its_definitions`). A definition on a
  cycle of families, or an instance body that binds a witness, owns memory
  at addresses no argument expresses -- every block reachable from its pointer
  arguments through the fields its body owns -- and those blocks are not
  known; nor is a clause that does not evaluate. Such a footprint is
  `MemoryRange::unnamed_footprint`, a range at a reserved symbolic block
  that no separation rule places apart from any cell, so it covers every
  cell except the ones the two rules below keep, which do not read the
  footprint at all. Which definitions reach unnamed memory is decided once
  per definition set, when a contract interface installs them
  (`src/kernel/owned_footprint_reach.rs`), so a recursive family costs one
  unit however many nodes are live
  (`a_recursive_footprint_is_constant_in_live_nodes`). Coverage questions
  -- a loop effect check, a refinement's containment, an Effect claim --
  read the unnamed footprint as covering every access. The footprint used to
  be enumerated by opening each held instance one body layer, and an
  instance with a named child, a matched body whose arm was not decided, a
  recursive or witness-bearing body, a nesting past eight layers, and a
  recursive composite the expansion left folded all contributed nothing, so
  a loop or call holding one was summarized as writing none of its memory
  (`mdtests/call_through_deep_instance_chain_footprint_includes_its_memory.md`,
  `mdtests/call_through_witness_footprint_includes_its_memory.md`,
  `mdtests/call_through_matched_arm_child_footprint_includes_its_memory.md`, and
  the earlier `mdtests/loop_binder_instance_footprint_includes_its_memory.md`
  and `mdtests/call_through_instance_footprint_includes_its_memory.md`). An
  exact footprint keeps a cell no clause owns
  (`mdtests/call_through_deep_instance_chain_keeps_a_cell_outside_it.md`,
  `mdtests/call_through_undecided_arm_keeps_a_cell_no_arm_owns.md`).
  The span over-approximates what a loop can write, so the loop head does
  not havoc a cell the enclosing function keeps owning outside the loop's
  declared resources: the body holds that cell only as a view and a store
  needs ownership, so the partition at the loop entry keeps it apart from
  anything the loop can come to hold
  (`mdtests/loop_body_cannot_write_function_owned_cells.md`). The kept cells
  are found through the kept context's base index, one lookup per cell.
- A call is the same argument at a call boundary. The callee's footprint
  over-approximates what it owns, so a cell an owned member of the caller's
  *residual* context holds keeps its value across the call: what the caller keeps
  once the call's consumed and borrowed resources are transferred
  (`CallKeptOwnership` in `src/kernel/primitives/memory_state.rs`, built by
  `call_kept_ownership` in `src/kernel/functions.rs`). At the call the
  transferred and residual resources form one valid composition, and owned
  memory is exclusive, so a byte an owned residual member holds is disjoint
  from every byte the callee can own, and a callee writes only what it owns.
  Residual field-bearing instances and non-argument-direct bodies stay
  opaque. `CallKeptRanges` shares the definition table and records the
  residual's composite facts through the persistent `owned_composite_facts`
  map. A kept read first checks listed flat ranges and views. It can then
  select a folded owner from a singleton bucket under an additive, indexed
  storage, class, or unique alias key, with a singleton block fallback.
  Only a selected argument-direct body is opened, and the resulting range
  must cover the whole access. Ambiguous lookups need explicit framing
  evidence. Diagnostics can enumerate the kept bodies on request.
  `kept_call_reads_do_not_scan_same_block_owners_or_aliases` covers hits and
  misses with growing same-block ownership and alias buckets.
  Ordinary C calls also retain the caller's pre-transfer composition as an
  exclusion index. After the listed and residual flat ranges fail, a positive
  flat owner covering the queried bytes rules out every unchanged residual
  composite: their owners were disjoint in that composition. The indexed
  base lookup never scans unrelated owners. Residual composites newly added
  by transfer or repackaging still participate, found by the persistent
  composite-map delta. The retained memory facts (including quantities) and
  added composites enter the kept-set identity, but never its diagnostic
  list of kept ranges. Views and zero quantities cannot exclude an owner.
  `a_transferred_flat_cell_does_not_open_unrelated_kept_composites` bounds both
  recording and a negative lookup beside 2, 4, 8 and 16 unrelated composites;
  positive controls keep new composites and retained flat fragments.
  Only exactly held bytes count: a residual *view* keeps nothing
  (the callee may hold its owner), an iterated clause in an opened body is
  skipped rather than counted at its span, a nested instance is not opened
  again, and an instance that cannot be opened (a matched body, decided or
  not, a guarded, recursive or witness-bearing one) keeps nothing: the rule
  keeps only bytes it reads exactly. Flat residual members are found
  through the residual's base index, one lookup per cached cell; opened ranges
  through theirs, then among the opened ranges of the cell's block when a
  reloaded base is proven equal to the opened one. The opening costs one
  evaluation of each residual instance's own body per call.
  The producer (`SymbolicMemory::with_call_memory_havoc`) and checker
  (`SymbolicMemory::matches_call_memory_havoc_result`) use the same candidate
  selection and `call_havoc_keeps_cell` rule. Whole concrete cells and seeded
  runs structurally contained in a flat owned atomic parameter object stay
  cached without visiting other retained objects. A persistent partition
  follows changed cells, runs and ownership ranges; ownership withdrawal,
  replacement by a view, or a wider cell forces reclassification. Ambiguous
  addresses and typed union views continue through the ordinary rule.
  Opened-instance cells still lose their cached value and are named across
  the edge at their pre-call value using the checked kept ranges and premises.
  `CallKeptRanges` retains an immutable indexed state of *all* flat residual
  owners and surviving views, including uncached members, plus the opened
  ranges and placement premises. The write-set marker uses a canonical identity for the complete
  range set: cached hashes select a bucket, exact persistent-map comparison
  decides equality, and globally unique identities distinguish unequal sets
  across threads. Diagnostics enumerate the ranges only when requested.
  Recording and comparing an unchanged retained frame therefore costs a
  persistent handle rather than a walk over every other parameter object
  (`a_call_records_kept_members_without_visiting_unrelated_residual_resources`,
  `a_call_records_aliasing_kept_members_without_enumerating_them`). A surviving
  flat view preserves its bytes under the checked stable-view call transfer
  (`mdtests/calls_keep_an_uncached_field_the_caller_views.md`). Its existing
  input index is shared in the frame identity; base and prepared address-class
  lookups select views without visiting unrelated ranges. This retains read
  values, never write authority. Conflicting borrows still refuse the call.
  The narrow atomic-parameter selection preserves the ordinary treatment of
  other cached cells; the arena pipeline remains a regression control.
  Exact flat borrows retain the caller's original checked partition instead
  of reconstructing and validating every old owner. Returned flat resources
  use incremental composition, checking each new owner and its conflicts.
  Ordinary unit returned composites carry one constructed body per emitted
  source occurrence, including acyclic owned/viewed nesting and decided
  conditional bodies. `ConstructedReturnBodies` retains each child's producer-assigned ID
  and parent, before normalization. Fixed consumed-input paths are selected
  from contract parameter bindings at entry; invariant borrowed footprints
  and actual allocation origin supply the other explicit transfers.
  Post-call loads do not acquire invariant-borrow authority. Body custody,
  allocation size and lifetime checks still apply to executed returns.
  Admission uses only the remaining unclassified ownership boundary, so cold
  or symbolic fallback cannot rediscover separation for transferred children.
  Prepared constant-coordinate memory leaves query the frame's address-class
  interval index; conflicts name the selected original held fact. Cold
  ownership queries can also use the raw interval trees and origin counts
  maintained by resource insertion/removal: a cold context needs no graph
  registration when all its owned memory shares the queried block and exact
  symbolic origin. The interval tree retains containing ranges even beside
  nested old intervals. Other blocks and origins remain unsupported on this
  structural route except physical automatic-storage partitions: the maintained
  automatic-owner index selects one storage block without visiting other locals.
  Loaded-pointer aliases still require the paired namespace.
  Symbolic narrow query endpoints may use directly indexed constant extrema
  to form a conservative enclosing interval against the supported constant
  owners. A disjoint envelope proves separation; an intersecting envelope is
  unsupported unless both endpoints are exact. Missing bounds stay bounded
  misses, without following order chains. Other
  symbolic boundary checks use the maintained summaries or retain the exact
  missing whole-frame separation premise. They never resume discovery, install
  a temporary combined context, revalidate the unchanged frame or the
  constructed body's internal partition, or scan the frame to name a conflict. Exclusive
  boundaries select the retained occurrence by resource or instance identity.
  Projections, packaged views and expansion caches reuse the same construction. Flat memory
  and token returns project directly, without generic composite expansion.
  An undecided body condition retains the opaque head; a decided false body
  produces emp. Viewed children keep their emitted source identities and
  stay views even when their definitions contain ownership clauses; they
  never acquire consumed-input, invariant-owner or fresh-allocation custody.
  A selected viewed expansion transfers only its exact source dependency,
  without enumerating equal-looking heads. Escaping borrow recovery retains the
  installed owner occurrence and gives each returned owner its own hold;
  consuming one equal-looking owner cannot release another's hold. Repackaging
  a borrowing head retains its selected input hold by ID even when the returned
  head's name changes; further returned owners receive additional holds.
  A returned borrow names a checked input by contract index or keeps its
  reserved input occurrence through an `owns` return. The caller looks up
  that source and checks the returned children against its retained permission.
  Inherited borrows maintain exact-resource and singleton-family permission
  indexes at creation/projection; a selected return never scans their growing
  projection histories. A failed nominee is final. Flat returned-view checks
  likewise select one caller occurrence and retain its checked binding in an
  opaque receipt; ledger use checks live holder/scope authority without
  re-proving that retained binding's permission. Whole-range permissions
  may back separate contained pieces, so keeping descriptions unmerged does
  not drop their holds. Adapter lends retain the producer-selected support
  occurrence rather than recovering an equal-looking head from the residual.
  Pointer-witness existential bodies may contain multiple witnesses and nested
  supported composite children, also under ordinary owned or viewed parents.
  The body producer retains the actual witness values keyed by the opened
  occurrence and each nested child's emitted parent/source identities;
  admission, projection and caches reuse that body without rebinding witnesses.
  Return construction never infers witnesses from held child descriptions.
  A selected definition's word-origin relations are indexed once, and argument
  identity is hashed once rather than once per witness. A witness-dependent memory description
  receives no invariant-parameter borrow or consumed-input custody. Only its
  actual fresh-allocation origin can grant allocation custody. This
  fragment never selects a witness from held composite children. Its optional
  normalization reads written endpoints/exact resource keys, selecting one
  neighbour per key without enumerating aliases or endpoint classes. A missed
  merge retains both facts. Internal composition still checks ownership using
  the full assumptions through incremental admission. Ordinary constructed
  returns use the same bounded normalization: a merge requiring discovery is
  skipped, preserving valid pieces and their recorded view occurrences. Guarded direct recursive bodies without
  named fields construct a finite frontier: open the selected
  body once and retain each recursive child with its emitted occurrence ID.
  Known deeper guards do not trigger further opening; an undecided root stays
  folded, and a false root contributes emp. Visible leaves use incremental
  admission and projections reuse this same construction. Recursive frontiers
  use the bounded optional normalization described above. Every return
  projection carries its one-level frontier, including explicit legacy
  projections; escaping-borrow recovery no longer reconstructs a missing frontier.
  Call precondition, canonical-entry, population-entry and dependent-return
  views now use their finite expansion directly. The obsolete second pass
  that repeatedly opened every decidable recursive tail has been removed;
  deeper opening requires explicit unfold steps.
  Flat, unmatched named instances now carry their selected field/argument
  values and emitted child occurrence IDs through return construction. Fixed
  parameter memory can carry a consumed-input reservation selected at call
  entry; model-field pointers do not acquire that custody by matching geometry.
  Fieldless authority controls carry the actual ledger count observations
  beside their emitted authority IDs. Exact exclusive-resource indexes check
  these authority leaves against the retained boundary, including when there
  is no memory conflict. Ledger identities are never recovered through pointer
  aliases. Flat matched named instances select one indexed constructor and
  retain its payload bindings and body; a missing constructor keeps the head
  opaque, without enumerating variant-refutation premises. Projection uses the
  constructed body without selecting the arm again. These named-instance
  fragments preserve the existing owned-unit clause restriction. Non-pointer
  witnesses, named children, field-bearing authority protocols and
  nested/recursive matched arms retain
  explicitly classified legacy routes. Specialized producers also return an
  explicit unsupported result for geometry outside the maintained ownership
  index; family dispatch remains separately classified. Ordinary constructed
  child partitions refuse unsupported geometry without retrying ownership discovery. A conflicting or invalid migrated body refuses the
  return rather than retrying legacy reconstruction.
  Monotone memory-evidence admission walks a smaller incoming contract or a
  shared persistent delta, without enumerating absent caller facts. Scalar
  refresh seeks only the equality class's concrete `local:` block interval,
  avoiding the opaque loaded-pointer members of linked parameter objects.
  A cold raw memory index chooses between its own occurrences and the closed
  graph's merge prefix, so a small contract never walks an unrelated caller
  history. Direct construction remains raw: it publishes no read authority.
  The input memory's variable-count index is prepared once during lowering;
  subsequent memory transitions advance an established index by their map
  differences, so a call does not reconstruct every preceding store.
  A copied resource context carries a copy of its memory index, so a query
  through the copy does not advance the original's. A proof step therefore
  synchronizes its execution state's index with its facts, and the contract's
  return-resource transition synchronizes the retained outcome's index before
  reading copies of it: a transition retried before each post-execution
  `have` then pairs only the facts added since the previous attempt
  (`post_execution_haves_before_a_fold_cost_the_same_at_every_position`).

### Queries

"Does the fact hold element `j`?" (`iterated_holds_element`) answers from the
index's range membership, the holes, and the guard cell at `j`: yes, no, or
*may hold* when the guard is not decided. A store is refused on *may hold*.
"Is the fact separate from this range?" (`iterated_separate_from_range`)
answers yes only for a range in another block or outside the span of every
element; it is the resource-separation prover's answer for an iterated
resource and never claims separation for a range that may hold an element.
Neither query reads more than one guard cell or the fact's own terms.

### Certificates, expansion, and cost

Each step records a `CheckedExecutionEvent::IteratedStep` from the checked
transition. Expansion prints it as written.

Indexed `unfold` and `fold` select one held clause by its exact instantiated
coordinates, then read one guard cell and the selected clause's holes. A store
reads the facts filed under its block. Folding or unfolding the declaring
resource moves one fact. Deterministic regressions measure work across range
sizes and with unrelated holdings.

### Declaration boundaries

- An unguarded clause must own the one-cell element `base[k..k + 1]` and
  lowers to `owns base[lo..hi]`; any other unguarded element is refused with
  that form.
- Guards compare `int32` cells with `==` or `!=`; an iterated clause owns one
  element range per index; a body declares at most one iterated clause, and
  match arms, contracts, and loop headers declare none.
- A call that may write the guard cells drops the fact rather than being
  refused; the loss surfaces at the next fold.
- When an instance folds, an owned memory clause whose range is provably
  empty is satisfied by nothing. A body such as `owns data[start..next]`
  must fold at `next == start`; before this slice that needed an empty fact
  left over from an earlier split.

## What stays out

Three things the tracker is deliberately not asked, because they are about
authority — "may I touch this" — rather than about versions:

- **resource occurrence identity** (`ResourceOccurrenceId`) and the **borrow
  ledger**. Borrows, shares and support bind to an occurrence; no proposition can
  name one, and the ledger's `BorrowLedgerStateId` is opaque and carries no delta.
  The borrow family is fail-open by design and must never be merged with the
  fail-closed families (above, and `src/kernel/borrows.rs`);
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
- **Chunk 3, also unrouted** — the proposition-level refusals (`solve_failure`,
  and an unclosed `have` whose goal matches an available fact up to a model-field
  version) print the field's source text now but do not yet reach
  `describe_resource_version_mismatch`: their callers hold two propositions and
  not the two saved states the answer needs.
- **From the map above** — the two duplicated retain closures are one function
  each now, `call_havoc_keeps_cell` and `borrow_preserving_havoc_keeps_cell`, so
  a producer and the checker that re-derives it can no longer drift apart by
  an edit to one of them. `call_havoc_keeps_cell` now requires range-disjointness
  evidence when a local cell has a range base in a different form; direct
  same-block construction transitions retain their existing behavior, while an
  assumed-equal alternate form drops the cached cell.
  The remaining *disagrees* entry is the difference between plain range
  disjointness and the rule's typed range evidence plus `_for_frame` composite
  expansion.

## Remaining ownership compatibility inventory

The source inventory in `build_support/ownership_fallback_edges.tsv` freezes
references to the APIs in `ownership_fallback_targets.txt`, using the existing
proof-search AST walker. Kernel and Surface production modules are checked on
every Cargo build; test-only modules are excluded. Calls, method references,
imports and macro identifiers are counted by file, owning type and function.
New references, changed counts and stale records fail the build. This is a
source dependency inventory, not a list of bugs or a complexity proof. A
compatibility wrapper can complete entirely in its fast path.

The incremental ownership-admission routes now use
`try_compose_checked_ownership_and_occurrences` and `returned_boundary_conflict`.
Raw output clauses, composite child construction, pending descriptions,
produced composite frontiers, stable-view recovery, worker completion and
loop-frame exchange do not resume ownership discovery on unsupported geometry.
Selected instance unfolds retain each emitted child's custody root. Loop-frame
restoration reuses that rule only when the selected root belongs to the loop's
original owned body. Removal withdraws the child's receipt; arbitrary additions
still require their boundary with the withheld frame. Emitted occurrences survive
restoration, and nested restores retain the same provenance.
Constructed groups retain their internal partition; admission checks only new
relationships to the destination frame. An indexed conflict refuses; a miss
retains a `ResourceSeparate` proposition naming the new range and actual
raw-memory frame. Function-call obligations expose that proposition for an
explicit proof. Existing loop/thread refusal wrappers may report the broader
exchange failure instead.

The bounded symbolic checker uses producer-published address and interval
summaries, including at most one selected symbolic neighbor. It checks direct
bounds for ordinary partitions such as `p[0..n]` beside `p[n..16]` with
`1 <= n <= 8`. Larger symbolic partitions can retain an explicit whole-frame
separation premise. Its memory leaves are indexed at fact admission; lookup
uses the selected range and canonical identity of the current frame, so a
proof about an earlier subset cannot authorize a new held range. The cached
frame footprint is prepared by ownership deltas, not by queries.

| Route | Current status |
| --- | --- |
| `EvaluatedReturnResources::admit_clause` | Carries checked entry-borrow and consumed-input selections from the checked call plan, including individually consumed finite input-frontier pieces, and checks them only against newly described outputs. Other outputs use bounded indexed admission. Unsupported geometry refuses; no discovery fallback. |
| `construct_composite_resource_body` | Held heads retain their selected source, frame and emitted child identities through body construction. Raw descriptions establish their missing boundary; generic composition admits only their new delta. Neither route revalidates the retained frame. |
| `PreparedReturnComposition::finish` | Consumes an opaque `ReturnedOwnershipPartition`. The producer's partition, including restored borrowed/consumed/fresh outputs, is retained; only pending outputs versus the original retained frame are checked. Returned pieces are not compared with each other again. |
| `produced_composite_frontier_conflict` | Constructed frontiers use bounded cross-boundary checks. Proven conflicts retain the selected held fact; unsupported geometry refuses. Family dispatch supplies every finite body; this consumer never expands a head. |
| `recover_candidate_stable_view_resources` | Consumes checked escrow restoration receipts carrying selected occurrences and holds. Restores the entry partition directly; checks only new return ownership against protected escrows and newly released inherited roots. No legacy ownership admission. |
| Worker completion and loop-frame exchange | Checked output groups and occurrence identities survive composition. Their generic boundary adapters remain separate compatibility consumers. |
| Family dispatch and `project_return_resource_cores` | Every returned composite or instance carries one constructed finite body or deliberately opaque head with its source occurrence. Unsupported family shapes refuse at dispatch. Boundary checks and projection consume this evidence without definition or memory arguments; neither reconstructs a body. |

Family dispatch has no legacy set or downstream expansion route. Supported
ordinary, existential, recursive, instance and authority families retain their
producer's children. Instances outside the specialized constructor fragment
remain deliberately opaque, retaining their exact occurrence and bindings.
Generic expansion previously left these instances folded too. A selected
instance with only logical fields and no body children introduces no hidden
memory cut point; its exact head and fields remain in the projection. Other
opaque instances retain their conservative ownership boundary.
For a nonrecursive matched instance with flat named children, dispatch can
retain a complete parameter-only envelope of all possible arms. This is boundary
metadata, not an unfolding: the head, model and child identities remain opaque,
and no views are published. Repeated alternative leaves are deduplicated; a
bounded admission constructs the supported envelope. Its leaves reserve the
same finite checked input supply as other returns, preventing input reuse.
Constructor-dependent child addresses and unsupported envelopes retain the
opaque boundary. Consumers never reconstruct this metadata.
Sealed field-free composites keep their certified finite frontier; seal
visibility does not erase internal memory boundaries. Iterated ownership is
carried as one finite descriptor leaf, without enumerating its guarded elements.
Missing definitions and unsupported field-free shapes refuse before publishing
a return. Counted bodies without exclusive leaves keep their count semantics;
a nonunit body exposing exclusive ownership refuses even when its leaves carry
input custody. Returned views retain their producer's child identities; there
is no description-only view receipt. Source guards forbid body production inside
projection and boundary consumers.

A direct `VerifiedFunctionRule` now travels through call preparation as typed
proof evidence, separately from concrete storage identity and description-only
interfaces. Its Hoare frame rule constructs the joint returned partition beside
the checked input reservation's caller frame. Arbitrary-shaped owned outputs,
including post-state pointer fields without an equality postcondition, need no
second geometry proof in this path. Normal and exceptional returns retain the
same rule, and entry escrow recovery uses the resulting partition token.
Targeted verification and expansion use the same Hoare frame rule under a
scoped source-contract hypothesis. That capability remains conditional, is
retired with the verification selection, and never certifies the unselected
body.
Named and callback application retains an `EstablishedFunctionContract`: the
instantiated interface plus the actual contract predicate premise selected for
that function value. That premise supplies the conditional Hoare frame rule
through selected direct calls, indirect calls and entry-escrow recovery. Bare
nominal declarations and discarded template bodies supply no authority, and
this capability never becomes concrete body-safety evidence. Missing or
inapplicable callback facts still refuse before application.
External descriptions and raw return APIs retain bounded admission and explicit
missing-boundary goals.
`verified_outputs_retain_the_callers_frame.md` and its expansion/replay test
contrast a verified callee with an uncertified external-output control.
`named_contract_outputs_retain_the_callers_frame.md` covers opaque pointer
outputs through both selected direct and abstract callback application;
expansion and replay retain the established contract premise.

Contract recipes retain immutable memory leaves from consumed heads as well as
flat consumed cells. Fixed byte spans can partition one consumed object into
disjoint field owners; the compiler withdraws each byte from its source interval
once, preserving bound formats and refusing duplicate fragments. Each selected
symbolic leaf is used once across all output paths;
postcondition equalities may connect a returned pointer field to an immutable
parameter. Model reads do not become parameter-invariant leaves. Typed parameter
identities and their unambiguous lexical aliases share the declared binder;
unrelated typed binders are never identified by spelling. Borrowed instances
reevaluate their model fields while retaining their checked entry custody.

Entry escrow recovery carries the return producer's partition token. Worker
completion additionally requires the parent ownership revision captured by the
thread ledger; public ownership changes or compiler-private registry changes
invalidate that receipt. Private scalar bookkeeping preserves it. Missing
receipts use ordinary checked admission. Allocation-class counters distinguish
callee automatic storage from external argument objects without visiting owners.

The old `PendingOwnershipAdmission` resume state and
`legacy_memory_boundary_conflict` are deleted. Their retired target names stay
in `ownership_fallback_targets.txt` so new references are rejected. Runtime
probes in `fallback_inventory_tests.rs` now require successful raw-output and
pending-return checks under `FastOperationScope`; the ownership-admission
scaling tests grow owners, aliases, explicit frames and removed-owner history.

Return-family dispatch retains finite bodies or deliberate opaque heads as
specified above. Unsupported shapes refuse at their classifier; projection and
boundary consumers never reconstruct a missing body.

The wider dependency perimeter must stay separate from that call-return
checklist. `ExecutionState::local_scalar_access_resources` and
`ReservedLocalScalarOwner::restore_into` admit withheld owners through
the checked incremental API. That API also serves exchange
restoration, certified groups, stable-view recovery, function resource
context evaluation, instance rewriting, contract refinement, iterated steps,
loop guards, proof-interface joins and thread joins. The manifest names every
caller and reference count. `try_compose_with_fact(s)` and delaying
normalization variants now use the same bounded incremental admission. The
retained context is a producer-established partition; explicit `validity_error`
remains available for validating raw assembled input. Composition does not
revalidate it. Normalized composition coalesces only changed occurrences and
bounded nominees from existing exact-resource/shape and constant-neighbor
indexes, plus a persistent index for symbolic written endpoints. Each
successful merge consumes a changed occurrence; a missed or borrow-bound nominee
keeps the split representation. It never walks aliases, related resource buckets,
projection caches or the unchanged frame to find another merge. Untouched
occurrences, supported projections and borrow dependencies keep their identities.

Generic held-composite expansion removes one actual parent occurrence and
constructs `HeldCompositeBody`, carrying that source, its residual frame and
its explicit body. Installation uses the held definition's separating-body
rule. It does not recheck body geometry or search the frame for equal children.
Viewed children receive only that parent's exact binding on their fresh emitted
occurrences. Selected return construction preserves raw clause order and
multiplicity. Optional normalization visits only the explicit body. Arbitrary
return descriptions still establish their cross-head and caller boundaries;
they do not acquire the held parent's frame rule merely from a role marker.
Cached expansion and live authority control expansion check reuse against the
retained ownership partition. Exact representations use the exact fact index.
For a split memory child, the indexed write supplier at each successive
address must start there, have positive quantity and compatible provenance,
and end at or before the child's end. Symbolic bounds follow the same
indexed endpoint chain used in owned-resource consumption. The walk stops
at an exact cover and
retains the existing occurrences and their lineage. No scratch context or
ownership validation is needed to establish coverage.
Generic expansion also serves contract entry/certification, folding and
observations, whose remaining caller-specific work stays source pinned. Footprint projection
coalesces the explicit ranges derived from its selected head without admitting
them again as new ownership; conservative overlapping arm unions remain unions.
Store framing similarly retains the selected held instance bodies' partition.
Returned-call recovery collects checked escrow receipts without rebuilding the
captured entry successor, checks the required output/escrow boundary, then
installs each receipt directly into the actual return context once.

Surface `unfold` constructs its body delta once before publishing definition
facts. It retains that successor and its emitted child IDs through publication;
it neither validates the whole projected context nor normalizes ambient buckets.
Known directly indexed collisions still refuse before a body fact can conceal
them. Fresh viewed children receive only the selected parent's binding; equal
ambient children keep theirs. A body already exposed by the same borrow retains
its existing child occurrences instead of emitting duplicate views. This reuse
uses bounded exact-child nominees and checks their retained borrow authority.
Control scratch reads and guarded-return entry reads also replace their selected
held wrapper with its declared children; they do not re-admit those children
against the caller frame or absorb equal ambient owners.
Population/control projection, selected callee
ownership reservations, loop declarations and loop-frame restoration use their
held or declared partition rather than raw caller-boundary admission. Their
actual reservation/consumption checks remain responsible for custody. Pointer
comparison builds its separation witness from the two distinct held flat
members selected from one resource context. Partial returns spend the input
frontier's actual fragments: distinct slices may share an original owner ID,
but the same bytes cannot supply two outputs.

Function completion retains the checked body's resource storage, including
split quantities, supported projections, borrow dependencies and occurrence IDs.
Ordinary returns, exceptional returns and void fallthrough do not call
`validity_error` or normalize the entire retained context. The borrow sidecar's
shared-root consistency check is constant work; selected output consumption,
borrow recovery and declared resource effects keep their own construction rules.

Entry/exit certification, definition-fact checking and Surface observation use
`observable_facts_assuming_valid` on their producer-established partitions.
They expose the compact observable composition without repeating ownership
admission. The raw `observable_facts` API still validates an assembled description
before publishing its facts. It is source-pinned as a raw boundary, so a new
fast-part caller cannot silently reintroduce whole-context validation.
The `exit_partition_tests` regressions preserve split occurrences across normal,
exceptional and fallthrough completion, reject overlapping raw observations,
and grow owners, related ranges, tokens, aliases and private slots at 4/16/64.
Existing observable-projection tests cover private filtering and invalidation.

For an explicit folded composite observation, the kernel takes the selected
resource and the memory naming input. It constructs the successor from the
reached state and publishes the checked body's views and structural
witnesses. An owned head supports its views through the selected occurrence.
A borrowed head publishes the new child descriptions to its live borrow and binds
the emitted occurrences to that borrow. An already-present exact child must
carry the same live borrow authority before it can be reused. The kernel
checks the introduced pure facts against the definition and checked
derivations.

Exact contract certification shares its original closing entry with the
single unconditional finite entry case. Guarded and recursive cases retain
their case-specific entry construction. Closing still needs the definition
and footprint evidence for each requested claim.

Normal `ensures` goal preparation and closing share one successful exit
resource projection per retained entry case. Reuse requires the same exit
checkpoint, adjusted memory and resource custody, composite definitions, and
proof facts including logical read definitions. A changed checkpoint prepares
a fresh projection. Each consumer builds its own claim state from the
projection, and closing still checks allocation escape and computes the
observation facts for its claims.

Deferred contract returns resume the boundary transition from the checked
body outcome. The boundary consumes all selected return clauses jointly
from that partition under the closing entry case. Individual resource
claim receipts carry the checked clauses for closing and allocation checks.
They do not replace body occurrences or supply a second source of ownership
to the deferred boundary.

Allocation escape checking retains the actual exit projection while
checking the returned resources. A flat partition can answer from its
owned allocation-token index. Call retirement reads the indexed tokens
of the input, output and preserved partitions. A retiring call with folded
resources in the preserved partition still projects that partition for the
stale-resource check. Input allocations are read in entry memory and output
allocations in successor memory.

Mutex call transfers install ledger-issued authorities using the exact
authority index. The publication load and its zero branch update the
selected subscriber right directly. Releasing a publication's payload
still crosses a resource boundary.

For a two-arm branch interface, Surface retains the written resource
descriptions in the provisional lowering state. The checked join
consumes those resources in both arms and constructs the owning
successor from their common residual and the selected interface.

Population authority proof steps construct the resource and creation-ledger
exchange at the reached execution state. Recording publishes that successor.
Replay checks the predecessor and the ledger transition identity before
reusing the retained successor.

The source tests in `tests/search_boundary.rs` pin the perimeter, including
new/hidden references and duplicate caller edges. Runtime probes exercise
raw-output admission and pending-return admission; the broader legacy routes
remain source pinned. Existing migrated fragment tests provide their own no-discovery/scaling evidence. The guard
observes registered discovery calls, not arbitrary loops: each future migration
still needs an operation audit and deterministic scaling checks.

Raw entry descriptions enter through `admit_declared_entry_resources`, before
the entry is published. It elaborates the declared section's known owned memory
frontier, including folded instance bodies and nested fieldless composites.
Admission reads the retained written-clause metadata, so normalization cannot
merge away repeated entry heads. It reuses the section producer's admitted flat
partition and admits only the newly elaborated body footprint beside it.
Nonunit ownership propagates through nested bodies and refuses a proven
nonempty exclusive footprint; empty ranges and readonly bodies remain allowed.
The returned context retains the original folded storage and occurrence IDs.
Undecided guards, unselected constructors, existential bodies and recursive
tails retain their conditional or opaque entry assertions; admission does not
guess a model or union mutually exclusive arms. It never inspects an unrelated
caller frame. Plain flat sections retain their existing section admission.

The raw constructor is source-pinned to the two entry producers. Initial,
outcome and unfold observations consume the resulting persistent composition
without whole-context validation. The actual Surface-helper regression grows
related owners, independent owners and aliases at 4/16/64. Legacy raw validation
visits are metered so an accidental return to that walk fails the growth test.
The folded-entry source regressions refuse duplicate ownership without an
explicit unfold and keep an adjacent owner accepted. Returned composite
requirements likewise consume every written body occurrence before normalization.
