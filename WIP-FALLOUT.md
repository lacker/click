# WIP fallout log

## nested_field_segments_keep_the_terminal_field_offset (first audit)

The write's `execute` now needs the defining equation (`v == load`) as a
theorem premise and fails: "condition-certificate premise search did not
derive int32 equality is true from 0 ambient condition facts: []". The
defining fact rides the CExpressionPath fact stream, but the
condition-certificate premise search consults an ambient condition-fact
channel that is empty at that point. Fix direction: route the defining
fact into the channel the premise search consults (find where
"condition-certificate premise search" collects its ambient facts and
whether path facts should feed it), or emit the defining fact earlier so
assumptions_with_path_context carries it into step certification. This
symptom likely underlies several of the 14 — verify against the next
tests before fixing one-off.

## Layer 1 fixed: the defining fact is certified, not derivable

`ExecutionPureFact::certified` (not `::new`) marks the defining equation
as kernel-certified by construction — the fresh variable is the kernel's
own name for the load. The "assumption-derived theorem premise without a
replayable derivation" class disappears across the affected tests.

## Layer 2 surfaced: kernel variables need surface spellings

Next failure class: "kernel fact has no recorded or structurally
synthesized Click spelling: ConditionIs(PointerOffsetEqual(Int32Scaled {
value: Variable(..)" — surface synthesis (frame certificate lowering)
must spell facts mentioning the minted variable. The fix direction:
when synthesizing a spelling for a kernel variable, resolve it through
its defining fact to the load's recorded surface spelling
(surface_synthesis-side), or record a surface alias at mint time via
the replay's surface record (lang-side plumbing at the drain boundary).
Re-diagnose the outcome-match class (Variable(2) vs certification
spelling) after this layer: the certified flag may have changed it too.

## Layer 2 progressed: substitution-based spelling, round-trip resolved

`resolve_minted_load_variables` (kernel/reasoning/substitution.rs,
exported) rewrites minted variables to their defining loads before
surface synthesis at the four surface_replay sites, and the round-trip
check now accepts a lowering that matches the resolved fact. Both
mechanisms work.

## Layer 3 surfaced: frame evidence bridges the two spellings

The remaining failure fact is
`ConditionIs(PointerOffsetEqual(Int32Scaled{Variable(v)},
Int32Scaled{MemoryLoad(..)}))` — smart-frame evidence relating the
minted-variable spelling of an address to its load spelling. Under
substitution it degenerates to a self-equality and its synthesized
spelling re-lowers as a TypedLoad fact — structurally unmatchable. The
right question is upstream: this premise is derived from the defining
equation (kernel bookkeeping, certified family) and plausibly should
never be surfaced as a user-facing frame premise at all, exactly as
certified store equations are not. Next session: read the smart-frame
candidate construction to find where premises are collected and whether
certified-derived offset equalities should be filtered into the ambient
channel instead of the surfaced premise list.

## Layer 3 fixed: bookkeeping derivations filtered from frame premises

Frame-certificate lowering now skips derivations whose conclusion
resolves to a syntactically reflexive equality under defining-fact
substitution (`proposition_is_reflexive_equality` after
`resolve_minted_load_variables`): those bridge the minted and load
spellings of one address, replay re-mints them deterministically, and
they are certified bookkeeping rather than Click-visible premises.

## Layer 4: outcome matching needs the equation chain

The test now reaches the outcome-match class: replay produces
`Return(Constant(7))` while kernel certification spells the outcome
differently, and pairing fails. The bridge needs chaining through the
defining equation and the store equation (v == load == value); check
whether `outcomes_match`'s definitional equality chains two equations or
needs the defining facts normalized into direct value equalities first
(normalize_direct_atomic_memory_loads exists nearby in the simp premise
path and may be the intended tool).

## Layer 4 infrastructure landed; the finding is fact flow

Two sound mechanisms are in: mint memoization (one canonical variable
per (snapshot arena id, pointer) — repeated loads reuse the name, so
self-relations stay syntactic) and `resolve_minted_load_pointer`
(range/containment provers rewrite a minted query address to its load
spelling before matching load-spelled owned ranges; wired into
`memory_write_range`). The decisive probe: the resolver finds ZERO
defining-shaped facts in the write check's assumptions during kernel
certification — the equation minted at lvalue evaluation is not in the
statement's fact context downstream. The next thread is execution fact
flow: where the lvalue path's facts go between evaluation and the
store's effective assumptions in the certification pass, and whether
defining facts need the persistent channel that certified store
equations use rather than the per-path stream. Also noted: the index
side of `data[len]` still embeds the raw len-load (pointer ADDITION
builds offsets outside the canonicalized helper), so the arithmetic
birth census needs the pointer-plus-int operator path added.

## Layer 4 continued: reuse-from-assumptions in, shape mismatch remains

The mint now searches ambient assumptions for an existing binding of the
same load (same pointer, same snapshot handle) and reuses that variable
before minting — the mechanism that should make the executed address and
the contract-spelled owned range coincide. It does not yet connect: the
lead test still certifies to MissingResource, so the contract's
variable-to-load linkage is not spelled as
`ConditionIs(Bitvector32Equal(Variable, MemoryLoad))` in the write
check's assumptions (or the snapshot handles differ between the entry
binding and the current-memory load). Next: dump the actual proposition
shapes mentioning the contract variable in this test's entry facts
(grounding, not guessing — candidate shapes include `CMemoryLoads`,
`Equal`, or a TypedLoad-anchored form), then widen the reuse match to
that shape, bridging entry-to-current memory through the existing
unchanged-load machinery if the handles differ.

## Layer 4 closed: content-addressed canonical load variables

The MissingResource class was a three-way spelling split for one load:
contract-grant lowering (surface, raw `MemoryLoad(empty-placeholder)`),
requirement evaluation (kernel mint from one counter), and body execution
(kernel mint from another counter). Counter-based minting cannot unify
passes that share no allocator state, so the mint is now content-addressed:
`canonical_load_variable(memory, pointer)` hashes the load identity into a
reserved id space (base 2^40, precedent `spec_fold_bound_variable`), with a
thread-local registry that panics on a hash collision between distinct
identities instead of silently conflating them. All three birth paths —
`mint_canonical_load_variable` (eval + spec) and the surface
`symbolic_pointer_contract_memory_load` — now call it, so every pass spells
the same load with the same variable and containment is syntactic. The
counter threading is now vestigial (parameters retained, unused) and can be
removed in cleanup. Lead test passes; suite fallout dropped 14 → 6.

## Remaining fallout classes (6 tests)

1. **Snapshot-unstable naming** (`truncated_service_step…`, likely the
   perpetual-service and simp-premise tests): the same cell loaded at two
   snapshots hashes to two canonical variables, where raw load spellings
   were previously bridged by atomic-load provenance seeing through the
   terms. Fix direction: canonicalize the load term to its
   provenance-stable spelling (store-equation / placeholder resolution,
   the existing `canonicalize_atomic_loads` layer) before hashing, so
   unchanged cells share one name across snapshots.
2. **No surface spelling for canonical variables in expansion**
   (`modular_call_snapshot_anchor…`, expansion tests): fact transports over
   defining equations have no recorded Click spelling. Same family as the
   layer-2 fix; extend the resolved round-trip or synthesize spellings for
   defining facts. The transport source also shows an un-canonicalized
   load born through the pointer-ADD operator path (worklist item).

## Snapshot-stable naming: canonical spelling + registry view (6 -> 4)

Two refinements landed. First, the canonical variable id now hashes the
provenance-stable spelling (`canonicalize_atomic_loads`) rather than the
raw term, so representational snapshot differences share one name. Second,
assumption-based cross-snapshot equalities (call-havoc boundaries) cannot
be hashed away, so equality reasoning views a registered canonical
variable as the load it names at the three trigger points
(`bitvector_terms_equal_for_memory_resolution`, the chase-pair check in
assumptions.rs, and `memory_load_terms_equal_for_fact_transport`),
letting the existing provenance evidence fire exactly as it did for load
spellings. The perpetual-service and truncated-service tests pass again.

Remaining (4): the resource-neutral-callee allocation fold and the
expansion separation `have` still miss — some resource/separation
matching path bypasses the widened equality; and the two expansion
transport tests need Click surface spellings for defining equations.
Also watch: full-suite time moved 19s -> 34s on one run; measure whether
the canonical-view recursion on the hot equality path is responsible
before integration.

## Frontier: resource-neutral-callee moved to the exit claim check

After the registry view landed, this test's failure moved past the fold:
the error is now `unverified claims: Ensure(0) = produces Composite
allocated(owner)` from src/lang/click/verification.rs:1120, and none of
the kernel MissingResource probes fire. Established so far: composite
candidate selection is spelling-insensitive (`exact_shapes` keys on
family/name/arity, resource_algebra.rs:656), so the miss is either in
`resource_fact_entails` argument-equality proving or — more likely given
the new error site — in the surface-level claim satisfaction comparison,
which may match produced claims structurally rather than through the
prover. Next: find where Ensure claims are matched against
replay-established claims in verification.rs and check whether the
comparison is structural; if so, decide whether to canonicalize claim
spellings at lowering or route the comparison through proof-aware
resource entailment.

Remaining failures (4): this one; expansion separation `have`
(source_expander_derives_separation_from_call_postconditions); and the
two expansion transport spelling tests (modular_call_snapshot_anchor,
snapshot_bridged_simp_premise) which need Click surface spellings for
canonical-variable defining equations. Probes still in tree: statements/
expression/functions MissingResource sites, resource_algebra write-miss
probe — remove before integration.

## Defining equations leave the path wraps (4 -> 3)

The resource-neutral-callee failure traced to `wrap_path_context`: call
postcondition equalities were being wrapped as
`Implies(defining-equation, equality)`, and the resource argument
equality path (`pointer_offsets_equal_for_memory_resolution` ->
`exact_condition_value`) does not discharge implications. A canonical
defining equation is true by construction of the naming, so both wraps
(`wrap_proof_facts`, `wrap_path_context`) now skip
`is_canonical_load_defining_fact` propositions, leaving consequents
unguarded and reachable by exact fact lookup. Suite time back to ~22s.
Remaining: the three expansion tests (transport spellings for canonical
variables, separation have).

## Canonical-name chain closure (3 -> 1)

Exact-premise checks in three consumers (step-using replay availability,
restricted-simp premise vetting in have proofs and its certification-side
twin, and `rewrite`'s exact-equality check) now close over pointer-offset
equalities chained through canonical load variables
(`premise_bridged_by_canonical_name_chain` in proof/fact_reasoning.rs):
a premise and the recorded facts may spell one user-level equality
through different kernel-internal names, and the closure is a bounded
BFS over equality facts with a canonical endpoint. The
snapshot-bridged-simp test's expansion no longer needs an explicit
transport step — its stale assertion was updated (a legitimate
certificate-spelling simplification, per the fallout-audit criterion).

Hard-won debugging note: adding ordinary locals to
`check_step_using_facts` overflowed the stack in
selected_pure_case_split_simp_expands_by_removal — that function sits in
a deep expansion-replay recursion, and in debug builds every added
frame byte counts. The closure call lives behind an #[inline(never)]
adapter so its work stays out of the recursive frame. The recursion
depth itself is worth an issue before integration.

Remaining failure (1): source_expander_derives_separation_from_call_postconditions.

## Last test: separation-derivation expansion (1061 passed / 1 failed)

`source_expander_derives_separation_from_call_postconditions` remains.
The smart separation derivation has one context premise spelled through a
canonical variable (`scaled(v1406...) == scaled(v100002)`, an init-ensures
equality), and `checked_surface_comparison_fact_at_point` cannot express
it in Click. Two resolution retries were added to the premise-spelling
loops in surface_certificates.rs (defining-equation based, then
registry-based via the new
`resolve_canonical_load_variables_from_registry`); the registry retry
advanced synthesis from "0 structural bases" to "1 structural bases",
but the load spelling sits at the call-havoc snapshot and no compatible
recorded snapshot exists at the proof point, so no replayable surface
spelling emerges yet.

Next ideas, in order: (1) check what spelling this premise had BEFORE
canonicalization (git stash the eval/spec migration and print the old
derivation premises) — the old load-spelled form found "compatible
recorded snapshots", so the recorded-snapshot matching may just need the
canonical view (viewed_as_memory_load) inside
checked_surface_comparison_fact_at_point's snapshot compatibility check;
(2) alternatively, premises that are pure internal-name bridges could be
exempted from surface expression when the replay-side canonical chain
closure makes them ambient — requires understanding replay_kind's
premise sufficiency contract first.

Probes still in tree (all env-gated behind CLICK_PROBE): contract_claims
ensure-resource, functions.rs definitional + registry, MissingResource
sites in statements/expression/functions, resource_algebra write-miss,
statement_step exact-premise. The CLICK_DISABLE_BRIDGE /
CLICK_DISABLE_TSKIP bisection gates in statement_step.rs and
surface_replay.rs must come out before integration.

## Suite green (1062/1062, 18.3s)

The last test closed when snapshot-indexed program points were computed
from the RESOLVED load spelling instead of the canonical-variable form:
`checked_surface_comparison_fact_at_point` now resolves canonical
variables (defining facts in scope, else the registry) before indexing
recorded snapshots, so the separation-derivation premise finds its
compatible point and a replayable Click spelling. Full lib suite passes;
time back to ~18s. Remaining before integration: strip probes and
bisection gates, run scripts/check.sh, the metadata-write budget
regression, and the position assertion from the issue's acceptance
criteria.

## Gate frontier: input-cursor example (lib suite green, examples gate red)

scripts/check.sh reached the examples gate; `examples/input-cursor` fails
at `input_cursor_shared_pipeline.contract` have proof 10: `transport(
at(statement(4).entry, left->data) == data, left->data == data)` finds no
certified connection. Grounded findings:

- At the base commit the reaches machinery never even ran for this
  transport (a base-worktree probe showed no load-shaped
  PointerOffsetEqual sources) — the target `left->data == data` at the
  current point was EXACTLY available in the fact set.
- On the WIP branch, `available` holds `v1406 == v100002` and
  `v1840 == v100002` but NO fact mentioning v1810, the canonical name of
  left->data at the current point. Three canonical names exist for the
  same cell at different effect points (their snapshots differ by
  call-havoc markers — correctly distinct, since equality across a call
  needs frame evidence).
- The regression is therefore in fact RESPELLING across effects: the old
  flow re-spelled load(m_pre, p) facts to load(m_post, p) under frame
  evidence as they crossed call statements, keeping current-point
  spellings available. Canonical-variable facts cross effects unchanged,
  so the current-point name is never connected.
- A transport hook in `transport_framed_atomic_bitvector`'s Variable arm
  (transport the registered load, re-canonicalize at the post snapshot)
  did NOT fix the example and DID break box_pipeline's step()-using
  premise — wrong site; reverted. The respelling that matters happens
  where step introductions/postcondition facts are carried across the
  statement boundary (check_step_using_facts' introduced-facts path or
  the kernel drain's cross-statement fact transport), not in that
  helper.

Next session: find where a `step() using`'s introduced facts and call
postconditions get re-spelled to the post-statement snapshot at base
(search for the old load-respelling on the introduction path, e.g.
`replay_available_across_effects` / drain transported facts), and add
the canonical-name analogue THERE: when the frame evidence rewrites the
underlying load, emit the bridging equality `v_pre == v_post` (or the
re-spelled fact) into the introduced fact set. Supporting changes kept
on this branch (all lib-green): canonical chain closure in the have
transport reachability, effect-window keyed on the registry-resolved
source, and the resolved-source assumption.

## Cross-effect respelling: binary-tree recovered, input-cursor remains

Session findings, all lib-green (1062/1062):

- The cross-statement automatic fact transport (transition_certification)
  now includes canonical-spelled facts (gate widened with
  `proposition_mentions_registered_canonical_load`), and
  `transport_framed_atomic_bitvector` transports a canonical variable as
  the load it names — resolving through a defining equation in the
  ambient assumptions first (mint-time spelling, live snapshot), falling
  back to the registry (canonicalized spelling).
- The snapshot-blind fact key now keys a canonical variable as
  `Load(registered pointer)` — one O(1) registry lookup, no snapshot in
  the key — so canonical spellings bucket with load spellings of the
  same cell. The candidate comparison resolves canonical names
  shallowly (term positions only, never walking embedded snapshots).
  IMPORTANT perf lesson: the first cut resolved with the full
  substitution walk per key/per candidate, and
  `collect_proposition_bitvector_variables` descends into embedded
  snapshot CELLS — that made a binary-tree `have` take 15s of unmetered
  wall time on ~1 deterministic unit. Anything walking whole snapshots
  is off-limits on these paths.
- A pairwise implicit-edge variant of the chain closure
  (memories-match per candidate pair per BFS node) blew binary-tree's
  5s simple-step budget and was removed.
- binary-tree, detachable-buffer, allocated-linked-list now pass.

input-cursor still fails (have proof 10 explicit transport). Latest
probe state: the introduction-loop transport for
`PointerOffsetEqual(scaled(v1406...), scaled(v100002))` still returns
ok=false even with defining-fact resolution in the hook — either no
defining fact for that variable is present in those assumptions, or the
resolved load's transport itself fails
(`memories_match_for_pointer_load` false for the mint-time snapshot vs
the post-call memory, and the directly-unchanged check too weak for the
call effect). Next: probe INSIDE the hook which alternative resolved and
why the load transport failed; if it is the directly-unchanged check,
compare against what base did for the same load spelling (base
transported these, so the same evidence must suffice — find which arm
accepted it at base).

## Origin registry and the shared transport-connect gap

The registry now keeps, per canonical variable, the first-seen ORIGIN
snapshot alongside the canonical (jumped) spelling
(`registered_canonical_load_origin`): the canonical spelling is right
for identity, but frame checks and snapshot indexing need the live,
DAG-connected origin. The transport hook and the registry resolver use
origins now; with that, the introduction respelling fires for some hops
(probes showed moved=true where the origin's cell survives) but not
across hops where the cell was clobbered and only effect-summary
evidence connects.

Both remaining gate failures are ONE capability gap, now precisely
characterized: an explicit `transport(at(P, e) == X, e == X)` must
connect a recorded-point canonical name to the current-point canonical
name across intervening effects. The evidence exists (effect summaries
/ store disjointness), but: (a) `c_memory_load_is_unchanged` on the two
ORIGIN snapshots does not compose across multiple effect hops and its
effect-fact arms demand exact memory identities that origin handles do
not always meet; (b) the origin-unchanged chain edges
(`premise_bridged_by_canonical_name_chain_with_origins`, wired into the
have-transport check with full-transition assumptions) therefore fail;
and (c) letting the resolved-load retry search freely reintroduces the
giant-term recursion — the motivating metadata-write mdtest burned its
full 2M-unit budget inside the have transport, and an isolated 8k fuel
bound on the retry cut the cost but broke
restricted_simp_certifies_unchanged_prefix_after_indexed_store (bound
reverted; lib suite green again at 1062).

The principled fix, for a fresh session: make the canonical name itself
stable across provably-disjoint effects at MINT time — the DAG epoch
keying (already in `canonical_load_variable`) returns None for these
snapshots because point-state memories lack derivation records; either
record derivations for replay point states, or extend
`cell_epoch_for_canonical_naming` to walk effect facts. If the entry
name and the current name coincide whenever the cell is untouched, the
explicit transports connect syntactically and no bounded search is
needed at all. Gate status on this branch: lib 1062/1062 green;
mdtests 395/397 (field_derived metadata-write, leaf_flag_grouped_simp);
examples red on input-cursor only.

## Approved design session: current-point respelling (2026-08-19, findings map)

The user approved option 1 (introduction-time respelling made complete;
fact sets stay current-point-spelled; transports search-free). One
session of implementation established, piece by piece with probes:

1. **Landed conceptually, needs clean re-landing** (all were verified to
   compile and pass the overflow test individually; the combination had
   2 lib regressions — expansion_preserves_unfolded_resource... and
   modular_call_snapshot_anchor... — unbisected when context ran out):
   - MutatesOnly-arm endpoint widening in c_memory_load_is_directly_
     unchanged via a never-inlined directly_matched_effect_endpoint
     (origin handles differ from effect endpoints by bookkeeping).
   - EffectSummary-arm deep-disjointness fallback
     (ranges_proven_disjoint_from_pointer) for composite-owned ranges.
   - CResourceSeparate transport in the framed prover
     (transport_framed_separation + _theorem + _atomic_memory_range, all
     #[inline(never)] with per-arm returns — a shared `conclusion:
     Proposition` local in the prover overflowed the expansion recursion;
     big enum locals are frame poison there).
   - CResourceComposition facts kept by assumptions_for_direct_fact_
     transport (owned-in-one-composition separations feed effect
     disjointness).
   - Separation bridging: MemorySeparate snapshot-blind key variant
     (Boxed! the inline tuple variant also overflowed), separation arm in
     propositions_equal_modulo_proven_snapshots (#[inline(never)]
     separations_equal_modulo_proven_snapshots comparing range parts via
     synthesized conditions after shallow canonical resolution), and the
     separation branch in snapshot_bridged_fact_is_available_under.
     THESE FIXED the metadata-write have proof 4 (separation transport).
   - The resolved-load search retry REMOVED from
     certified_fact_transport_reaches_through (it burned the whole
     2M-unit budget reconstructing the giant-alias recursion; with it
     gone the failures are prompt and cheap).
   - Direct start<->goal origins check in premise_bridged_by_canonical_
     name_chain_with_origins (bounded by isolated fuel 8k + per-call
     cache) — the connective for `true -> v_cur == v_entry` targets whose
     source lowered to Constant(true).

2. **The last diagnosed gap** (metadata-write have proof 6, input-cursor
   have proof 10): the origins-unchanged proof fails at any fuel because
   the store hop between origin snapshots lives in the memory DAG, and
   the origin handles (lowering-time copies with materialized cells)
   have no derivation records — the DAG walk cannot start from either
   side, and the effect-fact chain does not cover plain stores. Options
   ranked: (a) record derivations for point-state/lowering memories so
   origins are DAG-connected (the walk already matches endpoints
   pointer-relatively and crosses store edges with the full distinctness
   battery — likely the complete fix); (b) have the walk start from a
   DAG-connected sibling of a drifted handle.

Re-landing order: pieces are independent; land 1's items one commit at
a time against the full lib suite (the two regressions will bisect
naturally), then attack 2(a).

## Fresh-session re-landing (2026-08-19, second pass)

Landed gate-green in order: (1) the effect-arm widenings (933eb177);
(2) the separation bridging layer + composition facts + retry removal
(fb640a6a) — the metadata-write separation transport (have proof 4) now
connects, and transports fail prompt instead of by budget; (3) this
commit: the direct start<->goal origins check in the chain (bounded,
8k isolated fuel), the range-membership route on DAG store edges
(bounded the same way — per-edge work must stay bounded; range extents
retain raw loads and deciding orderings against them must come from
exact facts), and a chain-first early accept in the have-body
transport checker. In-place fact replacement for transported facts
(order-preserving) also landed, with the replacement in a never-inlined
helper (frame discipline).

Two footholds confirmed by probes this pass: BOTH origin snapshots for
the metadata-write bridge are DAG-connected (derivations present), and
the walk's blocking store edge is `data[len+1]` vs `owner->data`,
which the new range-membership route can decide when its ordering
facts arrive by exact spelling.

NOT landed: the automatic separation transport in the framed prover
(disabled — respelling separations at introduction changes expansion
premise selection; two pinned fixtures) — the helpers remain
#[allow(dead_code)] for when the selector question is settled.

Metadata-write frontier now: the 2M-unit burn moved to
`replay_available_across_effects(&target, ...)` — the bucket bridge's
modulo comparisons (`conditions_equal_modulo_proven_snapshots` ->
`memory_loads_proven_equal`) are UNBOUNDED and re-enter whole-snapshot
alias comparison when canonical-resolved loads cannot be decided
cheaply. The pattern is now clear across three sites: every consumer
that resolves canonical names to loads and asks general load equality
needs the same bounded-fuel discipline; the next session should bound
`memory_loads_proven_equal`'s deep legs behind isolated fuel at ITS
entry (one site instead of per-consumer whack-a-mole) and measure the
corpus for regressions from newly-prompt failures.

## Deep load-equality legs bounded at their single entry (suite green)

`memory_loads_proven_equal`'s two expensive tails — whole-snapshot alias
comparison and the framed-load prover — now run under one isolated node
budget at that entry, after every cheap route has answered. Lib suite
1062/1062; the availability-bridging burn site is gone.

The metadata-write budget burn moved into the DAG walk's new
range-separated store-edge arm: `range disjointness: derived
separation` burns ~1.6M DETERMINISTIC UNITS despite the isolated fuel —
fuel caps resolution NODES, not scan units; the derived-separation
candidate scan is unit-metered work that fuel does not bound, and the
walk re-asks it per store edge unmemoized. Next session, two options:
(a) memoize the per-edge disjointness by (write, pointer, assumptions
id) and make the derived-separation scan output-bounded; (b) a cheap
targeted route for the canonical case — write base and separation range
base share a canonical name, so membership needs only the extent
ordering, decidable from exact requires facts once their spellings
normalize (at-spelling vs live). Option (b) is the semantics the case
actually needs; (a) is the general hygiene both the scalability
contract and this walk want anyway.

## Scan-burn diagnosis complete (2026-08-19, handoff)

Two compounding causes behind the store-edge burn, both now located:

1. `pointer_in_range` (memory_reasoning.rs:918) falls from
   `exact_condition_value` to full `decide` per ordering, and
   `memory_separation_candidates` includes DERIVED candidates whose
   construction ("range disjointness: derived separation", 1.57M units)
   scans composition members pairwise — the eager-pairwise pattern the
   efficiency contract forbids on hot paths.
2. Every ad-hoc assumption context (the chain's fold-built
   chain_assumptions, transport_assumptions) has NO ambient memo id, so
   ALL the memoized provers (`c_memory_load_is_unchanged`'s memo,
   resolution-query memos) run COLD on every call from those sites —
   the walk re-pays full price per edge per caller.

Fresh-session plan, in order: (a) give `pointers_proven_disjoint_by_range`
its own resolution-query memo variant (new PointerRangeDisjoint key —
do NOT reuse PointerDistinct, the semantics differ on negatives);
(b) make the derived-separation candidate construction lazy/output-
bounded, or precede it with the exact-fact candidates only for the
store-edge caller; (c) consider content-hashing ad-hoc assumption
contexts so the existing memos engage (this single change likely
recovers most of the cost across all three burn sites — measure first
whether the id computation cost is acceptable, per the memo-id comment
in resolution_query_memo_id). Acceptance stays: metadata-write mdtest
under budget, input-cursor within 30s, full check.sh.