# named-memory-states arc (canonical memory, option C)

Status: in progress
Claimed: worktree-agent-a799da2cbca60970b (branch
`claude/nervous-ptolemy-90e738` in `.claude/worktrees/`) — 2026-07-30

Design brief: `../canonical-memory.md`. Failure corpus and per-member
diagnoses: `store-provenance-family.md` (that task stays parked; this
file is the arc that unparks it).

Scope boundary (owner, 2026-07-30): kernel/internal representation
only. No Surface Click syntax or semantics change. If the design seems
to demand one, stop that thread and record it under "For the owner".

## The problem, stated concretely

`Bitvector32Term::MemoryLoad(SharedCMemory, Pointer)` embeds a whole
memory *value* — `CMemory { blocks, cells }` — in the term. Two
spellings of the same location at two program points are therefore
structurally different terms whenever anything unrelated was stored in
between. Every prover that must relate them does so by bridging
*values*: `canonical_c_memory_deep`, `memories_match_for_pointer_load`,
`c_memory_load_is_unchanged`'s effect-summary scan, and
`load_unchanged_via_effect_chain`'s BFS over `CMemoryMutatesOnly` /
`CMemoryEffectSummary` facts. That BFS is *reconstructing*, from
recorded facts and at proof time, the write history that execution
already knew when it built the snapshot.

The whole store-provenance family is where the reconstruction runs out.

## The chosen shape (decided here; canonical-memory.md is silent on it)

canonical-memory.md specifies the destination ("a memory state is a
name, not a value; states form a DAG `m0` / `store` / `havoc` / `call`;
equality is select-over-store plus write-disjointness") but not the
migration. The migration decided here is **derivation-annotated
interning**:

- The `SharedCMemory` arena — which already exists, already assigns
  every distinct snapshot a dense `u32` id, and is already the identity
  used for `Eq`/`Hash` — *is* the name supply. Nothing new to thread
  through terms.
- Alongside each arena id we record **how that snapshot was produced**:
  `CMemoryDerivation::{Store, LoopHavoc, CallHavoc}`, each naming its
  base by `SharedCMemory`. Entry states have no derivation. That is the
  DAG, materialised.
- The `CMemory` value stays for now. Every existing reader of `.cells`
  / `.blocks` keeps working unchanged, so each increment is small.
  Readers are retired one at a time as provers move onto the DAG; the
  value view is the *last* thing to go, not the first.

Why not put the derivation in `CMemory` itself: it would land in
`Eq`/`Hash`/`Ord` (all derived today) and split identities that must
stay merged, or force five hand-written impls whose whole job is to
lie about a field. Keeping provenance outside the value keeps "the
derivation is metadata, never identity" true by construction.

### The two invariants that make this safe

**1. Advisory, never load-bearing.** A recorded derivation only ever
*adds* true facts (this snapshot is that snapshot with one cell
written). A missing derivation costs completeness and nothing else:
every consumer must fall back to today's path. This is what makes the
A/B flag meaningful and every increment revertible — and it is why
cross-thread handles (the arena is thread-local, so a snapshot interned
on another thread resolves to no derivation) are merely slower, not
wrong.

**2. Parent id < child id, so the DAG is acyclic by construction.**
Derivations are recorded **first-wins**: a snapshot that is already
interned keeps whatever derivation it already had. A derivation's base
must already be interned to be named, so its id is strictly smaller
than the id being recorded. Cycles are therefore unrepresentable —
including the two that would otherwise be easy to build: a store whose
value equals the cell already there (result content-equal to its own
base), and a store-then-store-back pair (the second result re-interns
to the first node and keeps the *older* derivation). A debug assertion
enforces the id ordering and a hop cap depth-gates every walk, per
conventions.md's rule about new recursive arms.

### Havoc identity, by construction (the soundness trap)

conventions.md: *never drop havoc/call-havoc blocks from canonical load
memories*; `memory_load_equality_does_not_ignore_loop_havoc_identity`
guards it. Two independent reasons this arc preserves it:

- The materialised `CMemory` is untouched — `with_loop_memory_havoc`
  still inserts the `havoc:N` block and still drops non-preserved
  cells. Every existing check sees exactly what it sees today.
- Havoc is a *distinct edge kind* in the DAG, not a store. The DAG
  walkers are written to relate loads only across `Store` edges whose
  written pointer is provably distinct, and across `CallHavoc` edges
  whose mutable ranges are provably disjoint from the pointer. A
  `LoopHavoc` edge is a hard stop: no walk crosses one, because loop
  havoc has no write set to be disjoint from. The freshness marker is
  therefore enforced at the edge, upstream of any snapshot comparison,
  instead of being re-derived from block names downstream.

## Staging

Every increment lands green on all four gates and is independently
reviewable. Flag: **`CLICK_DISABLE_MEMORY_DAG`** (conventions.md
naming) — set it and every DAG arm is skipped, restoring the previous
path exactly. Default is DAG-on; the flag is the A/B handle for
attributing behaviour and cost changes.

1. **Representation + recording** (no consumer). `CMemoryDerivation`,
   the arena side-table, `SharedCMemory::derivation()`, recording at
   the three edge producers (`CMemory::store`,
   `with_loop_memory_havoc`, `with_call_memory_havoc`). Behaviour
   identical by construction because nothing reads it yet; kernel tests
   assert the DAG shape after real execution.
2. **First consumer: `c_memory_load_is_unchanged`.** A DAG arm that
   walks `after` down to `before` across Store/CallHavoc edges,
   checking pointer-disjointness per hop and refusing LoopHavoc. This
   is `load_unchanged_via_effect_chain`'s job answered from ground
   truth instead of a fact-set BFS.
3. **Load equality in the atomic prover** (`atomic_load_equality_
   resolves`, the `proves` canonical/resolution arms): two loads are
   equal when their pointers are equal and their memories share an
   ancestor reachable without a conflicting write.
4. **Select-over-store evaluation**: `load(store(m, p, v), q)` reduces
   to `v` when `p == q` provable, else to `load(m, q)` — replacing
   parts of `canonical_memory_for_pointer_load`.
5. **Retire value-bridging**: delete `load_unchanged_via_effect_chain`
   / `c_memories_connected_by_effects` / deep-canonicalisation callers
   as the DAG subsumes them. Only then consider shrinking what
   `MemoryLoad` embeds.

Corpus order once consumers exist: `verifies_old_memory_loop_invariant`
and `fill_tail_keeps_first` first (same program shape, smallest repro,
0.04 s to fail), then owned-string, then the bubble/vector/field
mdtests.

## Session log

### 2026-07-30 (session 1)

Read the brief, the corpus, and `claude/forall-extension-wip`.

**Verdict on `claude/forall-extension-wip`: reject the rule, reuse one
diagnostic.** The branch is 293 lines over 3 files, two WIP commits on
top of a master that has since moved a long way.

- `forall_fact_extends_bound_by_one` (assumptions.rs) — reject. It is
  a bespoke arithmetic rule (`∀v<b` + final index ⇒ `∀v<b+1`) whose
  final-index obligation fails for exactly the reason this arc exists:
  the conclusion's load spelling drifts by snapshot. canonical-memory.md
  already recorded that making that match resolution-aware blew a 300 s
  budget. Landing it would be one more bridge begetting another.
- `equality_graph_terms_match_with_facts` (assumptions.rs) — reject as
  written, but it is the right *shape*: equality-graph node matching
  that consults framing instead of structure. It reaches for
  `c_memory_load_is_unchanged` under a reentrancy guard, i.e. it pays
  the value-bridging cost inside the hot equality graph. Revisit at
  stage 3, where the same predicate is a cheap DAG walk.
- `atomic_pointer_offset_equality_resolves` (assumptions.rs) — small,
  self-contained, and independent of this arc: resolution-aware
  `PointerOffsetEqual` mirroring the existing
  `atomic_load_equality_resolves`. Not adopted here (it is not on this
  arc's path and would need its own gate run and justification), but
  it is the one piece worth someone's separate commit.
- `invariant_closer_facts` (proof.rs) — reject on the branch's own
  evidence: store-provenance-family.md records that feeding
  `replay.effect_facts` into the closer "did not help since stores are
  execution facts, not effect summaries". That sentence is precisely
  the arc's thesis; the DAG supplies the execution facts directly.
- `proposition_conjuncts` visibility bump (api.rs) — only needed by the
  rejected rule.

Nothing from the branch is carried forward into stage 1.

## For the owner

*(nothing yet — no surface-semantics question has come up)*

## Dead ends

*(none yet this arc)*

## Done when

The acceptance corpus passes: examples owned-string and owned-vector
de-quarantine; mdtests vector_fill, field_derived, bubble_pass3,
bubble_sort3, composite_owner_buffer_field_dependent,
fill_tail_keeps_first de-quarantine; lib
`verifies_old_memory_loop_invariant` and the store-provenance-diagnosed
ignored tests un-ignore; and the explicit
`have at(statement(1).exit, selected) == ...` workaround in
`mdtests/proof_advance_pointer_local.md` deletes cleanly with
certificate generation finding the spelling itself.

## Repro commands

```
cargo nextest run --lib --bins                    # 497
cargo test --test mdtests                         # 271 visible
cargo test --test examples
cargo nextest run --lib --run-ignored ignored-only -E 'test(verifies_old_memory_loop_invariant)'
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=fill_tail_keeps_first cargo test --test mdtests
CLICK_DISABLE_MEMORY_DAG=1 <any of the above>     # A/B against the pre-arc path
```
