# Explicit have scripts cannot move onto the goal path yet

## Violated invariant

The drain's goal-based smart-`have` path should carry every `have` the
legacy checker carries. A sound (`--nocapture`) probe over the fixture
gates shows the goal path misses 1023 times per full run, and 77% of the
misses are fully explicit single-tactic scripts (`[Normalize]` 312,
`[Assumption]` 145 in mdtests alone) that `try_linear_smart_script`
declines *by design* — searchless scripts belong to explicit certificate
checking, and the drain site lacks the `check_certificate` branch the
scope drivers already have.

Adding that branch (attempted 2026-08-18, reverted) exposed two blockers
in `mdtests/field_derived_precise_effect_after_metadata_write.md`
(`buffer_push.contract`, statement 6, source tactic 6):

1. **Strictness policy**: three explicit have certificates there carry
   tactics after a goal-closing step. The legacy checker tolerates the
   redundant suffix; the strict `Proof` path rejects ("a tactic follows a
   goal-closing step"). Either the goal path gains bounded
   suffix-tolerance (mirroring its final-`simp` no-op rule) or the
   fixtures' scripts are cleaned — a policy decision, since the scripts
   are proof code, not C.
2. **Checker performance**: one of the explicit certificates consumes the
   entire 2,000,000-unit deterministic control budget inside
   `ProofScope::check_certificate` where the legacy
   `checked_have_with_proof` is cheap. Checking the same certificate
   through the strict scope path must not cost orders of magnitude more;
   this is a scalable-verification violation to reduce and fix before the
   dispatch lands.

## Reduction (2026-08-18, second pass)

The budget sink is isolated to one certificate shape in the reproducing
mdtest: a nested `[Have, TransportUsing, Assumption]` explicit body takes
19.2 seconds through `ProofScope::check_certificate` (its sibling of the
same shape takes 3 milliseconds), exhausting the 2,000,000-unit budget
inside the check. Timing attribution puts 1.34M units / 8.8s in kernel
"general alias: range" under "resource context equality" — per-candidate
alias queries during the nested transport's matching. Both paths end in
the same checker (`check_point_fact_transport_using_facts`); the
difference is the operation view: the goal path's `PointOperationView`
supplies replay-derived effect facts where the legacy point root supplies
the path's transition facts, and the byte-granular memory context of this
test makes the larger effect set explode the alias search. Next step:
compare the two views' input sizes at the slow have and bound or index
the transport's candidate enumeration (exact-first, alias-bounded), per
the complexity contract.

## Reduction (2026-08-18, third pass)

The input-size hypothesis is dead: at every explicit have in the
reproducing mdtest, the goal-path scope's fact context is identical to
the legacy `certificate_available` (43–46 facts, equal counts), the
transport view already supplies Path effect facts, and both paths end in
the same checker. Two certificates of the identical `[Have,
TransportUsing, Assumption]` shape with near-identical inputs cost 3
milliseconds and 19 seconds respectively — so the divergence is inside
lowering/matching for the specific propositions, not input volume. The
working theory is the recorded-versus-fresh lowering asymmetry the API
doc documents elsewhere: the legacy drain replay leans on recorded
surface lowerings (cheap membership at the cost of snapshot anchoring),
while the strict scope check re-derives the transport lowering and pays
full kernel general-alias cost on this test's byte-granular memory. If
so, the honest fix is kernel-side: bound or index the general-alias
range queries the fresh lowering performs (the attribution shows 1.34M
units there), not a return to recorded-lowering shortcuts.

## Attempt log (2026-08-18)

Extending the resolution-query memo to the general
`pointers_proven_distinct` (mirroring the bounded variant's
`PointerDistinct` key with a `PointerDistinctGeneral` variant) did not
move the budget: the reproducing have still exhausts 2,000,000 units.
Either the cell-pair queries do not repeat within one ambient context, or
`resolution_query_memo_id` returns `None` on this path (no ambient
assumptions scope, fuel armed, or DAG lookup depth nonzero) — the next
session should first count memo engagement (`key.is_some()`) at this call
site before optimizing further. The sub-attribution stands: 67% of the
range work is the `derived separation` fallback
(`proves_resource_separate` on 1-byte ranges per alias miss), so bounding
or short-circuiting that fallback under snapshot comparison is the other
untried lever.

## Reduction (2026-08-18, fourth pass — the mechanism)

Engagement counting kills the repetition theory: only 144
`pointers_proven_distinct` calls occur (136 memo-eligible), ~9,300 units
each — the cost is per-call, not repeated. Outcome probing then isolates
it: the `derived separation` fallback runs 166 times and returns `false`
every time — two-thirds of the range work proves nothing in this
workload. Its per-call price is structural:
`proves_resource_separate_inner` performs a linear scan over all
`prop_facts` propositions with per-separation-fact containment *proving*
(`proves_resource_contains_inner` twice per fact), then a composition
sweep and a coverage check — the complexity contract's named linear
exact-premise anti-pattern, executed per differing snapshot cell. The
fix's key lemma: `memory_separation_candidates` claims to project "the
same candidates" from compact compositions — if that index is complete
for memory separation facts, the linear `prop_facts` scan is redundant
for memory-memory queries and can be skipped (or the scan gains an
index), cutting ~900K units and bringing the reproducing have from 2.2M
units to ~1.3M, under its 2M budget. Verify the completeness lemma
against the index construction before landing.

## The completeness lemma, resolved (2026-08-18)

`adjust_memory_separation_fact` captures every
`CResourceSeparate { Memory, Memory }` and `CMemoryDisjoint` proposition
into the block-pair index at insertion, and compositions project through
`extend_composition_separation_facts` — so for memory-memory facts the
index is complete. The linear scan's residual value is exactly two
things the index cannot serve: separation facts where either side is
non-memory (a composite or token whose containment can still entail
memory separation through body unfolding), and any containment reasoning
that crosses block spellings (the index is keyed by base-block pair; the
scan's `proves_resource_contains_inner` is not). The
semantics-preserving fix is therefore a *residual list*: maintain a
dedicated small collection of separation facts not captured by
`proposition_memory_separation`, and rewrite the scan as index-first
(block-pair candidates, which the caller has often already consulted)
plus a linear pass over only the residual list — output-sensitive in the
number of non-memory separation facts, which is small. Cross-block
containment via provably-equal pointer bases, if it matters in practice,
stays covered by the residual pass only when the fact is non-memory; a
memory-memory fact reachable only through cross-block containment would
be a completeness loss, so the change needs a probe run over the gates
asserting no derived-separation outcome flips.

## Progress (2026-08-18: the residual list lands; the sink is containment proving)

The linear `prop_facts` scan is replaced for memory-memory queries by the
block-pair index plus a maintained residual list of non-memory separation
facts (other query shapes keep the full scan, since the indexed pass does
not serve them). A corpus-wide parity probe found 35 outcome flips — all
`legacy=false, indexed=true`: the composition-projected candidates were
invisible to the legacy scan, so the change is strictly stronger with
zero losses. It does **not** clear the reproducing budget: the 2M
exhaustion persists, so the true per-call sink is the per-candidate
containment proving (`proves_resource_contains_inner` twice per indexed
candidate) and the composition/coverage sweeps, not the enumeration. The
next profiling round should sub-attribute inside those.

## Leaf attribution (2026-08-18, final autonomous pass)

With the scan indexed, the remaining ~900K derived-separation units per
run split into two leaves: **indexed containment** (~492K — the same
block-pair candidates the caller already `pointer_in_range`-checked,
re-proven with the generalized containment machinery whose added power
over in-range is base-shift normalization) and **coverage** (~407K —
`range_covered_by_resource_separate_ranges`), with the fact scan and
compositions negligible. All of this is failing search: every one of the
166 distinctness queries returns false, inside a transport lowering the
legacy path serves from recorded lowerings. The remaining cut is a
design choice, not a mechanical one: either a bounded
snapshot-comparison mode for certificate-check lowering (skip
derived-separation retries whose cheap form already failed, noting a
truncation — weakens the strict checker exactly where the legacy checker
never searched at all), or kernel-side arithmetic speedups inside
generalized containment and coverage. The first preserves the
complexity contract by construction; the second preserves full search
power. Worth deciding together with the suffix-strictness question,
since both trade strict-path completeness against cost on the same
certificate shapes.

## Decision (2026-08-18): strict, with an actionable diagnostic

Extra suffix tactics after a goal-closing step are an error, and the
tooling now says exactly what to do: "the goal was already proved by the
previous step, so this `assumption()` has nothing left to prove; you can
delete this line" (with the claim and step index). Under that rule the
reproducing mdtest's three provably-dead `assumption()` suffixes are
deleted — the strict checker itself identified them — and the fixture
still passes on the legacy path, confirming they were dead for both
checkers. Blocker 1 is resolved. Blocker 2 (the budget-exhausting
certificate, whose own trailing `assumption` remains unverified because
the check dies first) is now the only thing between the dispatch and
landing.

## Root cause identified (2026-08-18)

The budget-exhausting certificate's cost is fully explained by
`issues/load-terms-in-arithmetic-positions.md`: its lowering touches
array cells addressed by loaded indices, and unresolved load terms in
those offsets make each alias query recursive. The remaining three
explicit haves in the reproducing mdtest already check successfully on
the goal path (394–3K units each) after the suffix cleanup; the dispatch
lands once the root fix makes the fourth comparable, with no bounded
checking mode.

## Intended regression

- A deterministic curve comparing goal-path versus legacy explicit-have
  certificate checking on the reproducing certificate shape (metadata
  write / field-derived effect context), pinning near-parity cost.
- The dispatch change itself (searchless scripts route to
  `scope.check_certificate`), landing only when the mdtest passes with no
  budget increase, plus a probe assertion that the have-miss count drops
  by the explicit-script share.

## Acceptance criteria

- `MDTEST_FILTER=field_derived_precise_effect_after_metadata_write` green
  with the dispatch in place and unchanged budgets.
- The suffix-tolerance decision is recorded in the proof-object API doc,
  and whichever side is chosen has a regression.
- The sound-probe have-miss count over the gates drops accordingly; the
  remaining misses are genuinely searching scripts.

## Simp chunk 2 scoping (2026-08-19)

The direct Simp path (claim_proofs.rs ~3585) admits a claim set only when
every open claim is `Ensure::Proposition` with no rewritten and no
frame-certified goal. Widening, in dependency order:

1. **Rewritten claim goals**: `rewritten_claim_goals[i]` holds the checked
   rewritten surface goal (produced via `focus_point_goal` +
   `SimpleProofStep::Rewrite`, with the rewrite certificate retained in
   `retained_certificate`). Admit these by pushing `(i, rewritten_goal)`
   into `direct_claims` instead of bailing; the direct proof proves the
   rewritten spelling and the retained rewrite certificate composes in
   the claim closure exactly as the legacy path composes it. Confirm the
   closure credit path before wiring.
2. **Frame-certified claim goals**: same shape —
   `frame_certified_claim_goals[i]` carries the frame-certified spelling;
   the direct attempt proves that spelling and the frame certificate
   composes. Verify whether such claims are already closed by the frame
   pass (`closures[i].is_closed()` guards them) and only the residue
   needs proving.
3. **`Ensure::Resource` claims**: need a typed resource-production goal
   on `Proof` (`begin_have` takes propositions only). This is the real
   API addition and connects to the substrate-4 typed function-outcome
   goals: a `produces R` goal focused per claim, discharged by the
   fold/consume machinery the legacy exit planner uses today. Land 1 and
   2 first; measure the remaining escape census (the 145-entry
   vocabulary measurement predates chunk 1) before designing 3.

Each step is gated: escape-census probe before and after, corpus parity,
`scripts/check.sh`.

## Simp chunk 2 census after step 1 (2026-08-19)

Rewritten claim goals are admitted to the direct path (landed 01dcd708,
gate green). A classifier census over both fixture corpora
(CLICK_CENSUS probe at the direct gate, --nocapture) counts the
remaining escapes to the legacy exit closer:

- resource-ensure: 191 (141 mdtests + 50 examples)
- frame-certified: 1 (single mdtest)
- non-ensure claims: 0

The typed resource-production goal (step 3) is therefore nearly the
whole remaining vocabulary; a claim set containing one resource ensure
keeps every claim on the legacy path today. Frame-certified admission
is a single-site follow-up. Design starting point for the resource
goal: `discharge_exit_simp_claim`'s grouped arm treats
`Ensure::Resource` as joining the grouped transition with no
proposition goal — the direct path needs the substrate-4 typed
function-outcome goal extended with a resource-production form whose
discharge runs the same fold/consume machinery
`resource_context_satisfies_definitional_fact` uses at certification.

## Grouped resource ensures: not closure-only (2026-08-19)

After the ungrouped slice (75ad9b74), 144 escapes remain, all
grouped-resource (94 mdtests + 50 examples; every example escape is
grouped). Marking grouped resource claims closed
`by_grouped_transition` with the direct certificate is NOT sufficient:
54 lib tests fail, led by grouped-simp expansion fixtures
(grouped_simp_expansion_preserves_resource_scalar_and_quantified_transitions,
expanded_execute_and_frame_replay_after_resource_branch) — the grouped
transition certificate must itself carry the resource transition
content (fold/production steps) that the legacy grouped closer builds
into it, not merely mark the claims closed. Next: read the legacy
grouped-transition builder (the code consuming
GroupedOutcomeSimpGoal/grouped_pending after the direct path) to see
what resource content it emits into path_grouped_surface_closers, and
either reproduce that content from the direct proof or extend
complete_point_obligations_since with typed resource-production
steps.

## Chunk 2 resource vocabulary landed (2026-08-19)

Three gate-green commits close the resource-ensure escape class:
ungrouped resource ensures (75ad9b74), grouped resource ensures via the
Assumption-padded grouped transition (63078245), and all-resource claim
sets closing without a proof attempt (this commit). The
compatibility-lowering fallback is gated to ungrouped attempts so
grouped sets needing nested-have spelling keep the legacy certifier
(pinned by outcome_predecessor_upper_bound...). Census across both
corpora: legacy-exit-closer entries 154 -> 81, of which 71 are direct
proof attempts whose goals the direct closures cannot prove yet (the
next vocabulary frontier) and ~10 are divergent/existence/frame
special cases. The remaining chunk items: strengthen the direct
closures against the 71 (measure which closure step fails), the single
frame-certified admission, then retire the legacy closer for the
converted classes.

## Attempt-miss breakdown (2026-08-19, post resource vocabulary)

The 71 direct-attempt failures split 38 ungrouped / 24 grouped (mdtests;
plus 7 examples-side, unclassified) with a diverse goal tail: predicate
calls needing scope-level unfold reasoning (permutation x15, valid_pool,
valid_capacity, sorted, sorted_pair), separation goals, plain result
comparisons (result >= 0, == 7 — likely needing outcome-value
substitution the compatibility lowering used to supply), and chained
implications. The grouped 24 are sets my compatibility gate now sends
to the legacy certifier — reclaiming them means teaching the direct
scope closures the nested-have spelling the legacy
certify_outcome_simp_have produces, which is the same work as the
ungrouped tail. This is incremental closure-vocabulary growth: pick the
largest classes (predicate-call goals, then result comparisons),
extend try_direct_logical_closure / try_simp_closure or add a
structured nested-have builder on the scope, one gated commit per
class.

## Predicate-call arm landed; grouped planner-candidate attempt reverted (2026-08-19)

`try_structural_simp_closure` gained a predicate-call arm (unfold the
goal once, refuse repeat unfolds, recurse) — gate green, converts a few
simple predicate goals; the big predicate classes (permutation etc.)
still miss because their unfolded bodies exceed the closure vocabulary.

A second attempt wired `certify_outcome_simp_have` (the legacy grouped
nested-have planner) into the grouped direct attempt as a checked
candidate per scope. Two findings before reverting to green:
(1) the planner's tactics establish the goal as a fact — a trailing
`Assumption` is needed to close the scope, mirroring the legacy
transition's per-claim closers; with it the nested proof completes.
(2) the resulting grouped surface script then fails COMPLETE replay
("`explicit proof script` surface certificate failed complete replay")
— the direct certificate's tactic stream, recorded into
path_grouped_surface_closers, does not replay at its position in the
explicit whole-contract script the way the legacy transition's stream
does. Next session: diff the two tactic streams for
drop_one.contract (legacy vs direct-with-planner) and align the
recorded form; the pinned test
outcome_predecessor_upper_bound_spells_a_rewritten_nonnegative_leg is
the reproduction.
