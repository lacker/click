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
  cell, and a memory block as a pure function reads it through an array
  argument. A byte range, a struct extent, a composite instance and a local
  are the kinds that come next.
- **program point** — a point on the current proof path (`entry`, a `mark`ed
  label, "here"), identified by the memory snapshot the kernel had reached
  there.
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

There is one decider, `resource_tracker::step_effect::affects`, and both walks
call it: "does this recorded step affect this resource?", answered `Affected`,
`Separate(how)` or `NotShownSeparate(check)`. A step kind is therefore answered
once, and a new one has to be answered for every resource before it compiles.
`Separate` carries what justified it — a checkable hop for a cell, a structural
claim about objects for a block — so `explain` and retained evidence say only
what was actually established.

| Recorded step | A cell | A block, as an array argument |
| --- | --- | --- |
| `Store` | separate on proven-distinct blocks, a common-base offset inequality, typed `separate(..)` evidence, an explicit range, general distinctness, or two owned members of one composition | separate **only** on `PointerBlock::proven_distinct` |
| `BlockDeclared` | separate: it writes nothing | separate when the declared object is proven distinct: it has its own `blocks` key, so this block's extent is the entry it was |
| `HeapAllocationPending` | separate | separate: a request with no address yet records nothing a read of a block consults |
| `ContractAllocationClaimsChanged` | separate | **stops** |
| `CellsForgotten` | separate | **stops**: the state is the same, the cell map is not |
| `HeapAllocated` | separate when the block differs | separate when the fresh object is proven distinct |
| `LocalLifetimeEnded` | separate on proven distinctness | separate when the retired object is proven distinct |
| `HeapFreed` | separate on three separation ladders | separate when the released allocation's object is proven distinct |
| `CallHavoc` | separate on range disjointness | separate when every declared range's object is proven distinct |
| `LoopHavoc(Some)` | separate under the extended-bridging and explicit-check gates, and never on the naming path | separate when every declared range's object is proven distinct |
| `LoopHavoc(None)` | never separate | never separate |

Two kinds still refuse a block outright, and both for want of a name on the
edge: `ContractAllocationClaimsChanged` names no allocation, and a contract
claim may cover a subrange of `ExternalArgument` memory; `CellsForgotten` names
no cell, so nothing says the values it dropped were not this block's. Recording
what they concern is what would settle either.

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
| two objects nothing separates | ``the store to `g[0]` may have written it, because `a` may point into `g`. If they are separate, require `separate(memory(a[0..1]), memory(g[0..1]))`; where the contract already transfers `g[0..1]` with `owns` or `consumes`, declaring `views a[0..1]` says the same.`` |
| a call or a loop with a write set | ``the call in between may write `g[0..1]` …`` then the same two clauses |
| the resource was written | ``the store to `a[i]` wrote it.`` |
| the read has no source spelling | ``the store to `g[0]` may have written it, and nothing tells that address apart from this read.`` |
| a fact about a block | ``a fact about `a` as a whole does not carry across the store to `b[j]`.`` plus the note below |

Every clause it proposes is one that verifies the situation it is printed for;
where none does, it says what is missing instead of naming a repair that would
not work. A whole-array fact is the case with no repair to name: the block walk
reads no stated separation at all, so the text says so rather than sending the
reader to write a `separate(..)` the walk will never consult.

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

This is the map of the kernel outside `src/kernel/resource_tracker/`, taken
against `origin/master` **48f960f8**. It exists so that the next reader does
not have to rediscover which of these sites are copies of the tracker's rule
and which are different questions wearing similar predicates. Line numbers
drift; the function names do not.

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
| `ResourceContext::invalidate_memory_support` → `memory_derivation_affects_footprint` `src/kernel/primitives/resource_algebra.rs` | **routed** | Walks the edges between two snapshots and drops every resource projection a step could have written. It now asks `affects` about `Resource::Ranges` for a stated footprint and `Resource::AnyMemory` for one the kernel could not name. |
| `ResourceContext::entries_affected_by_memory_derivation` | another question | Chooses *candidates* from the interval index; the rule then decides. Its one obligation is to stay a superset of the steps `affects` does not answer `Separate` for — narrowing it would silently keep a stale projection. |
| `statement_call_havoc_views` `src/kernel/proof/execution.rs` | another question | Collects the call nodes between two states; asks nothing about a resource. |
| `matching_recomputed_call_havoc_views`, `c_memories_definitionally_equal` `src/kernel/api/contract_certification/contract_claims.rs` | another question | Matches two derivation chains edge for edge, to certify a recomputation. A whole-state equality, not a footprint. |

### The eager half: a step applying its own write set

These run *at* the step, over every cell, in the producing context, before the
edge exists. Each decides the same abstract question as the matching arm of
`affects` and each decides it differently, so none is routed.

| Site | Class | Why it differs |
| --- | --- | --- |
| `CMemory::with_call_memory_havoc` retain `src/kernel/primitives/memory_state.rs` | disagrees | Keeps a cell on `local:` **or** `ranges_proven_disjoint_from_pointer`. The rule's `CallHavoc` arm has neither the `local:` disjunct nor the plain variant: it reads typed range evidence and the `_for_frame` expansion, which looks through composite definitions. Weaker in one direction, stronger in the other. The `local:` disjunct is sound only because a call's checked write set can never be based in a `local:` block — nothing in this function says so, and passing `&t` to a callee that owns `t[0..1]` is refused for want of `owns local:t@0[0..1]`, which is what enforces it today. |
| `CMemory::matches_call_memory_havoc_result` | disagrees | The same retain rule again, for the checker that re-derives the producer. It must stay identical to the producer, not to the rule. |
| `CMemory::with_loop_memory_havoc_preserving_loans` retain | disagrees | Preserved-block membership plus `LoanLedger::permits_memory_access`. An ownership question, with fail-open polarity, and no pointer-alias reasoning at all. |
| `CMemory::with_interface_memory_havoc_preserving_loans` retain | disagrees | Byte for byte the loop retain, in a second function. A join records no edge, so no rule covers it. |
| `CMemory::without_possible_aliasing_cells` | disagrees | `pointers_proven_distinct_for_memory_resolution`, **or** `pointers_directly_disjoint_by_range`, **or** `owned_composition_store_separated_evidence`. The second exists only here, deliberately: it is a range-index scan the rule's hot `Store` arm must not pay for. The third is shared with the rule's `Store` arm and the two transport sites, and it has to be here too: a cell this function drops is lost to every later route, because the two snapshots then differ at the read's own address. |
| `CMemory::without_field_cells` | disagrees | Same-block equality and a constant byte interval. Across blocks it removes too little, which for a copy is the safe direction; a completeness difference only. |
| `heap_allocation_may_contain_pointer` | disagrees | `base.block != pointer.block` answers "not contained", which is fail-open on a spelling. The rule's `HeapFreed` arm is three separation ladders instead. Reaching it needs a freed allocation whose base block is not proven distinct from a live cell's block. |
| loop frame assembly `src/kernel/loops.rs`, `collect_loop_effect_check_obligations`, the multi-exit join | disagrees | Each reinstates or drops cells against the loop's *stated* effect summaries rather than a recorded edge, with a hardcoded `local:` skip. |
| `memory_diff_is_covered_by_changed_pointers`, `memory_diff_is_covered_by_ranges` `src/kernel/proof/execution.rs` | another question | The containment direction: is every observed change *inside* the declared write set. The tracker has no containment question. |

### State versus state: "do these two snapshots agree about this read"

The tracker's `same` answers this for two points on one recorded history. These
sites answer it for two snapshots that need no ancestry — an effect summary's
endpoints, a recomputed chain, a canonical form — so `same` cannot replace
them without losing every pair the DAG does not connect.

| Site | Class | Note |
| --- | --- | --- |
| `c_memory_load_is_directly_unchanged`, `memories_directly_match_for_pointer_load` `src/kernel/memory_provenance.rs` | disagrees | The transport rule. It already asks the tracker as one disjunct — two snapshots that name the cell by one point hold the same cell — and the rest reads `CMemoryMutatesOnly`, `CMemoryEffectSummary` and `CHeapAllocationFreed` over *stated* endpoints. Its per-write ladder is the same four predicates the rule's `Store` arm uses, applied to a stated write list. |
| `memories_match_for_pointer_load` `src/kernel/reasoning/memory_resolution.rs` | disagrees | Assumption-free structural agreement about one load: equal havoc markers, equal extent for the load's block, and equal cells under `observable_by_load`. Decides pairs with no common ancestor. |
| `memory_snapshots_match_for_resolution`, `memories_match_for_pointer_load_bounded_alias`, `memories_match_for_pointer_load_under_assumptions` `src/kernel/reasoning/memory_resolution.rs` | disagrees | The same question with assumptions: every cell the two snapshots differ on must be proven distinct from the load. All three refuse a load whose own block is `local:`, and all three select the cells to check with `cell_is_observable_by_load`, the one filter — *not*, as they used to, by dropping every differing `local:` cell unasked. See below. |
| `canonical_memory_for_pointer_load` | separation | A normal form, so that two snapshots can be compared at all. Its filters are `observable_by_load` and `cell_disjoint_from_load_by_constant_offset`, one shared function each. |
| `memories_proven_equal_for_memory_resolution`, `memory_cells_definitionally_contained` | another question | Whole-state equality under assumptions. |
| `differing_cell_pointers_possibly_aliasing` | separation | One call to `observable_by_load`. |

### The separation predicates, which stay one function each

`affects` has no overlap logic of its own; it asks these. They are listed so
that a fix lands in one of them rather than beside it.

| Predicate | Home |
| --- | --- |
| `PointerBlock::proven_distinct`, `may_alias`, `observable_by_load`; `Pointer::blocks_proven_distinct` | `src/kernel/primitives.rs` |
| `pointers_proven_distinct_for_memory_resolution`, `pointer_offsets_with_common_base_proven_distinct`, `cell_disjoint_from_load_by_constant_offset` | `src/kernel/reasoning/memory_resolution.rs` |
| `range_proven_disjoint_from_pointer`, `ranges_proven_disjoint_from_pointer`, `ranges_directly_disjoint_from_pointer`, `ranges_proven_disjoint_from_pointer_for_frame`, `frame_frontier_compositions`, `pointers_directly_disjoint_by_range` | `src/kernel/assumptions/memory_reasoning.rs` |
| `typed_store_separated_ranges_evidence`, `typed_ranges_disjoint_from_pointer_evidence`, `heap_allocation_proven_separate_from_pointer`, `owned_composition_store_separated_evidence` | `src/kernel/memory_provenance.rs` |
| `memory_block_may_alias`, `memory_range_overlaps_pointer`, `memory_ranges_overlap`, `proves_resource_separate`, `proves_owned_range_separate_from_pointer_with`, `resources_structurally_separate` | `src/kernel/primitives/resource_algebra.rs` |
| `MemoryLoadAliasCache::resolution_distinct` | `src/kernel/eval/memory_loads.rs` — a per-load memo over the first of these, not a rule of its own |

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

One pointerless neighbour still carries the shortcut and is not part of this
fix: `memories_proven_equal_for_memory_resolution` compares whole snapshots
with the `local:` cells and blocks filtered out, and
`PureFactContext::has_order_path_for_memory_resolution`
(`src/kernel/assumptions/condition_reasoning/order_paths.rs`) uses it to decide
that two memory loads at one pointer are the same term. It has no load pointer
to ask about, so making it exact is a separate change with its own blast
radius. The false theorem above does not reach it: the order-fact form of the
same attack (`have q[0] < 6`) is refused.

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

Cost: `#owned × #viewed` clauses of one contract, built once at that contract's
entry and never on a query path.

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
a retired allocation is skipped rather than refused; and the
`held_child_witness` filter accepts `own.block != pointer.block` as "a
different pointer" with no proof, which selects a witness rather than proving
anything.

## Next chunks

- **Chunk 2** — one question, asked one way. The step-side deciders are one
  rule now; what is left is settling the block column's remaining blanket
  refusals, one commit and one regression each.
- **Chunk 3** — the other resource kinds. Register the "changed here" events
  for composite instances, occurrence identities and loans, so `same` and
  `explain` cover model fields too.
- **From the map above** — the two duplicated retain closures (call havoc
  against its own checker, loop havoc against the interface join) are one rule
  written twice in one file each, which the map calls *disagrees* only because
  they disagree with `affects`. Making each pair share one function is a
  behaviour-preserving change that the next chunk can take first.
