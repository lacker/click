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
| `Store` | separate on proven-distinct blocks, a common-base offset inequality, typed `separate(..)` evidence, an explicit range, or general distinctness | separate **only** on `PointerBlock::proven_distinct` |
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
| two objects nothing separates | ``the store to `g[0]` may have written it, because `a` may point into `g`. If they are separate, require `separate(memory(a[0..1]), memory(g[0..1]))`.`` |
| a call or a loop with a write set | ``the call in between may write `g[0..1]` … require `separate(memory(a[0..1]), memory(g[0..1]))`.`` |
| the resource was written | ``the store to `a[i]` wrote it.`` |
| the read has no source spelling | ``the store to `g[0]` may have written it, and nothing tells that address apart from this read.`` |
| a fact about a block | ``a fact about `a` as a whole does not carry across the store to `b[j]`.`` plus the note below |

Every clause it proposes is one that verifies the situation it is printed for;
where none does, it says what is missing instead of naming a repair that would
not work. A whole-array fact is the case with no repair to name: the block walk
reads no stated separation at all, so the text says so rather than sending the
reader to write a `separate(..)` the walk will never consult.

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
| `CMemory::without_possible_aliasing_cells` | disagrees | `pointers_proven_distinct_for_memory_resolution` **or** `pointers_directly_disjoint_by_range`. The second exists only here, deliberately: it is a range-index scan the rule's hot `Store` arm must not pay for. |
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
| `typed_store_separated_ranges_evidence`, `typed_ranges_disjoint_from_pointer_evidence`, `heap_allocation_proven_separate_from_pointer` | `src/kernel/memory_provenance.rs` |
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

One kind of evidence a contract can state still does not reach a load:

- **a separating resource composition.** `owns value[0..1]` beside
  `owns Cell(result)` in one context says the two are disjoint, and nothing on
  the load path asks. The predicate cannot simply be reused: the rule's `Store`
  arm (`src/kernel/resource_tracker/step_effect.rs`, `cell_effect`) has no
  composition disjunct at all — its ladder is `blocks_proven_distinct`,
  common-base offsets, `typed_store_separated_ranges_evidence`, shallow explicit
  ranges, then the general query — and the composition route
  (`ranges_proven_disjoint_from_pointer_for_frame`) is *deliberately* kept off
  the per-cell path: "whose per-cell store-drop callers must not pay for an
  expansion they never need". Adding it is a new route and a per-cell cost
  decision, not a reuse.

##### Parked proofs

Three proofs state true claims that the missing route would prove, and
stopped being provable when the name filter went. They are quarantined rather
than weakened: their C and their sidecars are untouched, so each is the
regression for the route it waits on
(`docs/internals/testing.md`, *Quarantine*). Unquarantine an entry in the
change that gives it its route.

| Parked | Needs |
| --- | --- |
| `mdtests/c_contract_executes_acquire.md` | a separating resource composition as evidence for one cell: `[owns value[0..1], owns Cell(result)]` |
| `surface::tests::expansion_tests::acquired_callback_ownership_expands_at_every_smart_site` | the same; it `include_str!`s that mdtest's fixture, so the two move together |
| `mdtests/const_callback_field.md` | the same, for `owns object(r)` beside `views p[0..1]` — the equality hop already resolves the read to `p` |

The loan family — `LoanLedger::permits_memory_access`,
`protected_range_proven_overlapping`, `active_memory_overlaps` — is **not** in
that list. It is fail-open by design and its soundness rests on the ownership
partition rather than on the predicate (`src/kernel/loans.rs`), so it must
never be merged with the fail-closed families above.

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
