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
| `BlockDeclared` | separate: it writes nothing | **stops**: it changes the extent a read of the block is checked against |
| `HeapAllocationPending` | separate | **stops** |
| `ContractAllocationClaimsChanged` | separate | **stops** |
| `CellsForgotten` | separate | **stops**: the state is the same, the cell map is not |
| `HeapAllocated` | separate when the block differs | **stops** |
| `LocalLifetimeEnded` | separate on proven distinctness | **stops** |
| `HeapFreed` | separate on three separation ladders | **stops** |
| `CallHavoc` | separate on range disjointness | **stops** |
| `LoopHavoc(Some)` | separate under the extended-bridging and explicit-check gates, and never on the naming path | **stops** |
| `LoopHavoc(None)` | never separate | **stops** |

The block column's blanket refusals are what two separate sets of hard-coded
answers left behind; they are findings to settle one at a time, each with its
own regression, now that there is one place to settle them in. The difference
that stays is *what evidence a resource may spend*: a block may use only the
kernel's structural separation, because its answer is embedded in a name that
is shared across proof paths, and the rule enforces that by handing the block
arm no fact context at all.

Two consequences a user meets today:

- an array fact dies at a step that writes nothing (a bare `int32 t;`), while a
  cell fact survives it;
- a stated `separate(..)` carries a cell fact across a call and does not carry
  an array fact, because the block walk has no fact context to read it from.

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

No recorded step carries a source span or statement text today, so a step is
described by kind and target ("a store to `g[0]`", "the call", "the loop"). A
line number would mean adding a source location to the `CMemoryDerivation`
edges at their producers in `src/kernel/primitives/memory_state.rs`; the edge
may carry it, since a span is path-independent.

## Next chunks

- **Chunk 2** — one question, asked one way. The step-side deciders are one
  rule now; what is left is settling the block column's remaining blanket
  refusals, one commit and one regression each.
- **Chunk 3** — the other resource kinds. Register the "changed here" events
  for composite instances, occurrence identities and loans, so `same` and
  `explain` cover model fields too.
