# named-memory-states arc (canonical memory, option C)

Status: in progress
Claimed: worktree-agent-a799da2cbca60970b (branch
`claude/nervous-ptolemy-90e738` in `.claude/worktrees/`) — 2026-07-30
Claimed (stage 2a): branch `worktree-agent-a9b0d0d8a52de5913` in
`.claude/worktrees/` — 2026-07-30
Claimed (stage 3): branch `worktree-agent-ae96555419eb6923f` in
`.claude/worktrees/` — 2026-07-31 (landed; stages 4–5 unclaimed)

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
2a. **`old(...)` gets a name** (inserted 2026-07-30 after stage 1 diagnosed
   it; landed session 2). Certificate replay resolved `old` positionally, to
   the enclosing region's execution-start state, while the Click → Spec
   lowering the kernel certifies against names function entry. Replay now
   carries the function-entry snapshot explicitly and resolves `old` — and
   `at(function.entry, ...)` — to it. Reads no derivation edges, only arena
   names, so it is not flag-gated.
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

**Landed:** stage 1 — `CMemoryDerivation`, the arena side-table, recording
at the three edge producers, `c_memory_load_is_unchanged`'s DAG arm, six
kernel tests. Gates: lib+bins 503 (497 + 6 new, ~8 s), mdtests 271
visible (~10–16 s), examples (~4 s), and the same three green under
`CLICK_DISABLE_MEMORY_DAG=1`. No measurable cost from the extra interning
at store time.

**What the DAG arm actually adds today.** Measured, because the first
draft of the test was vacuous. `memories_match_for_pointer_load_under_
assumptions` already takes the two snapshots' differing cells and
requires each provably distinct from the loaded pointer, so a plain store
to a distinct cell needs no DAG. Its real limit is the line above that:
it first requires the two snapshots' **non-local block sets to be
identical**, so it refuses outright once anything changed the block set —
which is exactly what a call havoc does when it inserts its
`call-havoc:N` marker. The recorded edge still carries the call's mutable
ranges, so the walk crosses it for a pointer provably outside them. That
case is pinned by
`derivations_carry_a_load_across_a_distinct_store_but_not_across_havoc`
and verified to fail with `CLICK_DISABLE_MEMORY_DAG=1` and pass without
it. Worth knowing when judging later stages: the DAG's leverage is
histories the *net snapshot diff* cannot express, not single distinct
stores.

**`old` has no name — the next increment.** Probed
`verifies_old_memory_loop_invariant` (the smallest corpus member) against
stage 1 to see whether the DAG arm moves it. It does not, and *why* is
the finding:

The DAG arm is never even reached on that path. Candidate lowering fails
first. All 36 surface candidates lower fine, including the one with the
right shape — `p[0] == old(p[0])`. But its `old` operand lowers to the
**loop-entry** memory `{blocks: havoc:1000001, local:i}`, while the
kernel certified the invariant with its `old` operand at the
**function-entry** memory `{blocks: {}, cells: {}}` (genuinely empty: the
symbolic `arg-memory` block is never registered in `blocks`). Two
different memory states, both spelled `old`, so no placement of the
operands can reproduce the certified fact — and the reported failure
("no placement of the comparison operands at the 4 recorded program
points lowered to the certified fact transport") is that mismatch, not a
weak load-equality prover.

This is precisely canonical-memory.md's `old(...)` references a named
earlier state. Today `old` references nothing: it is resolved
positionally at lowering time to whichever earlier state the lowering
context happens to hold, and the kernel and the certificate lowering
disagree about which one that is. Stage 1 supplies the missing names, so
the next increment is to make `old` resolve to a *node* rather than to a
context, on both sides.

Note this stays inside the scope boundary: the surface text `old(p[0])`
does not change. Only which memory state the lowering resolves it to.

Consequence for the staging above: the stage order needs one insertion.
`old`-resolution becomes stage 2a, ahead of the atomic prover work,
because it is what actually gates the two smallest corpus members
(`verifies_old_memory_loop_invariant` and `fill_tail_keeps_first`, same
program shape). Stage 2's DAG arm stays landed and is exercised by the
kernel tests; it will start paying once the operands can be placed.

Sequence for whoever picks this up: find where loop-preservation
certificate lowering resolves `ClickProposition::Old`, compare it with
the state the kernel's certified fact was built against, and make both
name the same DAG node. The 36-candidate enumeration is in
`verify_certified_fact_transport`'s `find_candidate` closure
(`src/lang/click/proof.rs`, near the "no placement of the comparison
operands" message); `comparison_program_point_variants` builds the
placements.

### 2026-07-30 (session 2) — stage 2a: `old` gets a name

**Landed.** `old(...)` no longer resolves positionally.

*The two pipelines and where they disagreed.* A Click contract clause reaches
the kernel down two different paths, and each answers "which memory does
`old` mean" separately.

- Click → Spec (`lowering.rs`, `AnnotationLowerer`). `ContractExpression::Old`
  switches the elaboration context to `old_state(...)`, whose memory is
  `SpecMemory::Fixed(self.entry_state.memory())`. `entry_state` is the
  function's entry `CState` (`environment.initial_state`), so the *kernel*
  side already names function entry — unambiguously, and for loop invariants
  as much as for `ensures`.
- Click → Proposition (`checking.rs`,
  `lower_outcome_proposition_with_environment` and friends). Here `old` is
  simply `pre_state`, a positional parameter. Certificate replay filled that
  parameter from `TacticReplayState::execution_start_state`, i.e. *the state
  this proof region started executing from*. In a whole-function replay that
  is function entry and everything agrees. In a loop-preservation region it is
  the loop-top havoc snapshot, and the same surface text meant two different
  states on the two sides.

That is the whole of `verifies_old_memory_loop_invariant`'s failure. Probed
and confirmed: the certified source was
`load(m{havoc:1000001, local:i}, p+k) == load(m{}, p+k)` — the `old` operand
at the empty function-entry memory — while the best candidate lowered both
operands at `m{havoc:1000001, local:i}`. No placement of the operands could
reproduce it, because no surface spelling available to the replay named the
function-entry snapshot at all.

*The fix.* `TacticReplayState` gains `function_entry_state: Option<CState>`,
the snapshot this region's `old(...)` names, and a `old_reference_state()`
accessor that answers the "which memory is `old`" question in one place. The
two loop-preservation planners (`plan_automatic_loop_preservation_body`,
`verify_one_loop_preservation_proof`) set it from
`environment.initial_state` — literally the same `CState` that
`annotated_function` handed the `AnnotationLowerer` as `entry_state`, so both
sides now name the same interned node. The 18 call sites that fed
`execution_start_state` into contract lowering switched to
`old_reference_state`; the two that genuinely mean "where execution started"
(re-running the function for kernel certification, and the join entry state)
did not. `None` keeps the previous positional answer, so every region that
records no function-entry snapshot behaves exactly as before.

`at(function.entry, ...)` moves with `old`: it is the same reference under
another spelling and `concrete_program_point_state` reads the same parameter.
On the Spec side those two already shared `old_state(...)`, so this makes the
agreement total rather than partial.

*How it is validated, and why that is not "trust the name".* Selecting a
state by name only adds a spelling to the candidate search. Acceptance is
unchanged and is the real check: `find_candidate` keeps a candidate only when
its lowering is *equal* to the certified proposition, and a `MemoryLoad`
carries its `SharedCMemory` inside the term, compared by arena identity. A
candidate resolved to the wrong state therefore cannot match — a
misresolution costs completeness, never soundness. This is why no separate
"is this really the entry state" predicate was added: the certificate check
already is one, and a second, weaker check would only be able to disagree
with it.

*Why this increment does not read derivation edges.* It uses the arena
*names* (interned identity), which predate this arc and are not flag-gated;
it reads no `CMemoryDerivation`. So `CLICK_DISABLE_MEMORY_DAG=1` gives
identical results rather than the pre-fix ones. That is deliberate: the flag's
contract is "derivations are neither recorded nor read", i.e. an A/B handle
over *completeness*. Resolving `old` is a question of what a spelling
**means**; gating that on the flag would make the flag change meaning instead
of completeness, and would leave the wrong resolution reachable. Both modes
were run and are green on all four gates.

**Acceptance corpus movement** (each retested individually):

- `verifies_old_memory_loop_invariant` (lib) — **passes; un-ignored.**
- `fill_tail_keeps_first.md` (mdtest) — **passes; de-quarantined.** Same
  program as the lib test, as store-provenance-family.md predicted.
- `composite_resource_vector_fill_loop_snapshot.md` — still fails (~5.6 s),
  and the message moved off `old`: "could not replay invariant closer:
  invariant 1 is missing path goal". Stays quarantined; this is the
  back-edge closer, stage 3/4 work.
- `bubble_pass3_max_suffix.md` — still fails (~10 s), invariant closer missing
  a `ForAll` path goal about the symbolically extended bound. No `old` in the
  failure. Stays quarantined.
- `bubble_sort3_two_pass_sorted.md` — still fails (~10 s). Stays quarantined.
- `composite_resource_owner_buffer_field_dependent.md` — still fails (~5.8 s).
  Stays quarantined.
- `field_derived_precise_effect_after_metadata_write.md` — still fails, and
  still grinds: **496 s**. Unchanged from the recorded ~500 s. Stays
  quarantined.
- example `owned-vector` — still fails (~8.5 s), same invariant-closer
  `ForAll` path goal as vector_fill. Stays quarantined.
- example `owned-string` — still fails (~2.5 s), same missing
  `loadable(...)` pure fact. Stays quarantined.

So stage 2a clears exactly the two members whose diagnosis was `old`
resolution, and the remaining corpus is now cleanly attributable to the
invariant closer rather than to spelling drift.

**Gates.** lib+bins 510 (509 + the un-ignored test, ~3 s), mdtests 272 visible
(~9 s), examples (~5 s) — green, and green again with
`CLICK_DISABLE_MEMORY_DAG=1`. Bit-identical outcomes in both modes, as
expected from an increment that reads no derivations.

**Next.** Every remaining corpus member fails in the invariant closer, on a
`ForAll` path goal it cannot re-derive. That is stage 3 (`load equality in the
atomic prover`) with a concrete target: the closer's goals are exactly the
snapshot-spelling drift the DAG arm was built for, and now that operands can
be placed, stage 2's landed `c_memory_load_is_unchanged` arm should finally be
on the path.

### 2026-07-31 (session 3) — stage 3

**The stage-3 target was not what the corpus said it was.** Stage 2a handed over
"every remaining member fails in the invariant closer on a `ForAll` path goal",
with the expectation that the goal needed load-equality across snapshot drift.
Diagnosing `composite_resource_vector_fill_loop_snapshot` end to end says
otherwise for the vector-shaped members: **the closer was being handed goals
that are true only vacuously, and could not see the vacuity.**

*The mechanism, measured.* `evaluate_c_memory_load_paths` resolves a load by
walking the snapshot's cells and, for each cell it cannot prove distinct from
the loaded pointer, splitting into an aliasing path and a distinct path
(`CMemory::first_unresolved_same_block_cell` +
`add_pointer_offset_equality_execution_pure_facts`). For
`(owner->data)[k]` at the back edge that produced five paths — one per owner
field, one for the store cell, one for "distinct from everything". The three
owner-field paths carry the guard "this element's address *is* `owner->cap`"
(resp. `->data`, and the trailing padding slot) and a goal of the form
`owner->cap == value`, which nothing can prove. They are vacuous: the resource
declares `separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap]))`,
so an element with `0 <= k < cap` cannot be an owner field.

Why the splitter did not prune them, and why the closer could not close them,
are the same fact seen twice. `verify_invariant_checks_at_back_edge_using`
lowers with `defer_non_exact_condition_reasoning()`, and under that flag the
range-containment prover refuses the order chain that puts `k` inside
`data[0..cap]`. Probed directly at the split site: with the flag, distinctness
is unprovable; without it, provable from the *same* facts, and provable from
the bound guard alone. So the paths get emitted, and then the closer — which no
longer defers — has every fact it needs to refute the guard but no rule that
looks.

*What landed.* `Assumptions::is_inconsistent` gained
`alias_guard_refuted_by_separation`: an assumed
`PointerOffsetEqual(a, b) = true` is a contradiction when recorded separation
puts `a` and `b` in disjoint ranges of one block. The vacuous paths then close
by `Explosion`, which is what they always were. Two details worth keeping:

- **Recovering the block.** `pointer_equality_condition` drops to a bare
  `PointerOffsetEqual` exactly when the two pointers share a block, so the
  guard no longer names it. The rule re-attaches the base block of a *separated
  pair whose two ranges share a block*, which is not a guess: separation
  constrains offsets only in that case, so the question asked is "do these two
  offset terms fall in disjoint intervals of one block", a statement about the
  offset terms alone.
- **`pointer_in_range`, not the memory-resolution variant.** The first version
  used `pointers_proven_distinct_for_memory_resolution` and cleared the mdtest
  but not example `owned-vector`, whose `preserve` script does not `unfold` the
  resource and so reaches the containment by a longer order chain. Measured on
  that context: `pointers_proven_disjoint_by_range` = true while the
  memory-resolution variant = false, with containment holding on exactly the
  right pair. Scanning the separation facts directly with `pointer_in_range` is
  both the semantically right predicate and the one that works.

Reentrancy-guarded (containment re-enters condition reasoning, which reaches
`is_inconsistent` again). Not flag-gated: it reads no derivations, so
`CLICK_DISABLE_MEMORY_DAG=1` is bit-identical, exactly as for stage 2a.

#### The bubble members: the load bridging already worked

The two bubble mdtests are the members whose missing goal really is a load
comparison across two snapshots — `load(m, p+k*4) <= load(m', p+j*4)`, where
`m'` is `m` plus cells for `local:j` and `local:tmp` and nothing else. The
expectation was that this needed a DAG walk. Probed: it does not.
`decide(load(m, p+j*4) == load(m', p+j*4))` is already `Some(true)`; the
existing bridging handles differing cells in a provably different block. With
the right-hand side rewritten by hand the goal was *still* underivable.

What is actually missing is one case split. The goal's guard is `k < j + 1`
while the invariant fact's is `k < j`, and probing both halves separately
showed each is derivable as it stands: below `j` from the invariant, at `j`
from the body's own effect (which, after the swap, makes the two sides of the
comparison the same value). Only the split was absent.

**Landed:** `PropositionDerivationRule::UpperBoundSplit` and
`derive_by_upper_bound_split` — an assumed `k <= b` (spelled either
`k < b + 1` or `k <= b`) splits a goal into `k < b` and `k == b`. Notes:

- It is a **goal-side** split, which is why it works where
  `claude/forall-extension-wip`'s `forall_fact_extends_bound_by_one` did not
  (session 1 rejected that rule because proving the final index meant matching
  a fact spelled at another snapshot). Here each half is derived in the
  ordinary way against whatever is present, so no spelling has to be matched.
- Sound at the wrapping edge: `k < b + 1` with `b = INT_MAX` wraps to
  `k < INT_MIN`, which is unsatisfiable, so the split's disjunction follows
  vacuously. The `k <= b` spelling has no edge case.
- Confined to leaf goals with an undecided pivot, and depth-gated to one
  level. Two levels were tried for the nested-loop member and bought nothing
  (158 s vs 137 s).

**Acceptance corpus movement.** One member now *passes* but is too slow to
un-quarantine; three more moved off the invariant closer.

- `bubble_sort3_two_pass_sorted.md` — **passes**, in **137 s**. Stays
  quarantined on cost alone (mdtest limit is 30 s), per conventions.md's
  slow-but-passing rule. Attribution below.
- `bubble_pass3_max_suffix.md` — `loop(0).preserve` now certifies. Fails later,
  in `max_at_end` path 0: "smart `simp` closed the claim but its certificate
  did not lower or replay: planned `simp` context premise is not an available
  source fact", the premise being the loop-exit invariant `ForAll`. ~8.9 s. A
  certificate-lowering gap, not a prover gap — and note the two-pass version of
  the same program does not hit it.
- `composite_resource_vector_fill_loop_snapshot.md` — closer now closes. Fails
  later, in `contract` path 0 tactic 2: grouped `simp` cannot certify its
  claim transition for `ensures_2` (the exit spelling of the same `ForAll`).
  **~47 s**, up from ~5.6 s, because the proof now gets much further.
- example `owned-vector` — `vector_fill.loop(0).preserve` closes. Fails later
  and elsewhere: `vector_replace_if.contract` tactic 8 `have` cannot find
  `Implies(replace == 0, new == old)`. ~9 s.
- `composite_resource_owner_buffer_field_dependent.md` — message moved off the
  closer to "execution proof for `set_owned_first.ensures_0` path 0 changed
  more than the certified ghost resource representation" (~5.7 s).
- example `owned-string` — unchanged (~2.5 s), still the missing
  `loadable(data[len])` pure fact. Untouched by this session's work.
- `field_derived_precise_effect_after_metadata_write.md` — not retested
  (~496 s to fail; not worth the wall clock until it has a reason to move).

**Where `bubble_sort3`'s 137 s goes** (`CLICK_TIMINGS=1` plus a 20 s `sample`
of the debug binary). One tactic, `loop(1).preserve` step 2 `simp`, is 64.6 s;
the rest is outside tactic timings, i.e. the invariant-closer replay inside
loop-rule verification. The sampled profile is not
`atomic_derivation_premises` (the cost recorded in
`store-provenance-family.md`) — it is dominated by
`reasoning::bitvector_terms_equal_for_memory_resolution` and
`api::canonicalize_atomic_loads`, under a haze of `Bitvector32Term` clone and
`BTreeMap` churn. That is the value-bridging machinery this arc exists to
replace, so the cost item and stage 5 are the same item: the DAG has to
*subsume* deep term-equality search, not sit beside it. Worth knowing before
anyone tries to make this test fast by tuning the split — the split is not
where the time is.

**Gates.** lib+bins 512 (510 + two new kernel tests, ~3.1 s), mdtests 272
visible (~9 s), examples (~7.0 s, up from ~5.3 s — `owned-vector` now runs
further before failing). Green, and green again with
`CLICK_DISABLE_MEMORY_DAG=1`.

**Stages 4 and 5 not started.** Stage 4 was gated on stage 3 landing green,
which it has, but no corpus member de-quarantines yet and the next failures are
all downstream of the closer (certificate lowering, ghost-resource
representation, contract `simp`). The profile above says stage 5's subsumption
question is the one with leverage.

## For the owner

*(nothing yet — no surface-semantics question has come up; the `old`
finding above is internal resolution, not surface semantics)*

## Dead ends

- Expecting stage 1's `c_memory_load_is_unchanged` arm to move
  `verifies_old_memory_loop_invariant` on its own. It cannot: probes
  confirmed the function is never called on that path, because
  certificate-candidate placement fails upstream of any load-equality
  question. Recorded above.
- **Validating `old`-resolution by a derivation-DAG ancestry walk** ("the
  named entry snapshot must be reachable from the current snapshot by
  following `base` edges"). Probed and rejected: the chain does not connect.
  For `fill_tail` the loop-top snapshot walks back
  `LoopHavoc -> Store -> Store -> Store` and stops at arena id 0,
  `{blocks: [local:i], cells: {}}`, which carries **no derivation** — the
  block that declaring a local creates is not a recorded edge kind. The
  function-entry snapshot is a *separate* root (id 3, `{}`). So entry states
  and executing states sit in disjoint components of the DAG today.
  Reachability could be restored with a fourth edge kind for block
  allocation, but it was not worth it here: it would have to be recorded at
  every block producer, it risks displacing `Store` edges through first-wins
  on content-equal snapshots, and it would buy a *weaker* check than the one
  the certificate comparison already performs (see the session log). Worth
  knowing before anyone else reaches for an ancestry walk: **arena identity
  is connected, arena derivations are not.**
- **Reading stage 2a's handover as "the closer needs better load equality".**
  It says every remaining member fails in the closer on a `ForAll` path goal,
  which is true, but three distinct causes hide behind that one message, and
  none of the three was load equality (2026-07-31, all three measured):
  vacuous alias paths the closer could not refute; a missing final-index case
  split; and, downstream of both, certificate lowering. The load bridging the
  arc built in stage 2 was already answering the questions put to it — probe
  `decide(...)` on the two spellings before assuming otherwise.
- **Using `pointers_proven_distinct_for_memory_resolution` for the alias-guard
  refutation.** It cleared the mdtest and not example `owned-vector`; the
  memory-resolution containment path is fuel-bounded and depth-limited and
  refuses the longer order chain that the plain `pointer_in_range` accepts.
  Measured side by side on `owned-vector`'s failing context: by-range true,
  memory-resolution false, same facts.
- **Raising the final-index split's depth limit to reach nested loops.**
  `bubble_sort3_two_pass_sorted` has two nested loops and closes at depth 1;
  depth 2 cost it 20 s and changed no outcome. Likewise, confining the split
  to leaf goals with an undecided pivot is right on principle but measured
  neutral — the 137 s is not in the split.

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
cargo nextest run --lib --bins                    # 510
cargo test --test mdtests                         # 272 visible
cargo test --test examples
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=vector_fill cargo test --test mdtests
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=bubble_pass3 cargo test --test mdtests
CLICK_EXAMPLE=owned-vector cargo test --test examples
CLICK_DISABLE_MEMORY_DAG=1 <any of the above>     # A/B against the pre-arc path
```

`field_derived_precise_effect_after_metadata_write.md` takes **~500 s** to
fail; bound it with `MDTEST_TIME_LIMIT` and do not put it in a loop.
