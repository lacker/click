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
