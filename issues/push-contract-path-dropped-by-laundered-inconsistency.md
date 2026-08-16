# Push contract path dropped by laundered inconsistency

## Violated invariant

Every execution path of a function must be certified by exactly one proof
context. On master (a3bc2333), `allocated_vector_push.contract` in
`examples/owned-vector` verifies while its `grown == 1` path (the outer
`owner->len == owner->cap` branch where `vector_grow` succeeds) is **never
checked**: no context certifies its ensures or its effect claim.

Mechanism, traced with closure-site instrumentation on a probe worktree at
master: `finish_ordered_proof_replay` runs three finishes (inner-then,
inner-else, outer-else). The inner-else finish — the only owner of the
`grown == 1` path — skips its path in the exit drain because
`fact_conflicts_with_assumptions(not (grown == 0), routed_assumptions)`
returns true, with the comment-promised justification "the sibling branch
certifies this path". No sibling does: the inner-then finish certifies only
the `grown == 0` return-0 path and the outer-else finish only the
`len < cap` path. The spurious conflict comes from launder-collapsed load
spellings (`canonical-load-jump-launders-havoc-markers`, fixed on this
branch) making the routed assumption context inconsistent, and in an
inconsistent context every case fact "conflicts". The skip silently
converts an inconsistency bug into a dropped proof obligation.

## What honest verification now requires (landed on this branch)

With the marker fix, the path is correctly attributed to the inner-else
context and must actually be proven — for the first time. Landed
machinery, each with the smallest sound rule that closes a real gap:

- `extract` accepts a discharged implication consequent (bounded modus
  ponens) in both pure-theorem and have-proof replay
  (`discharged_implication_consequent_is_available`,
  `src/lang/click/proof/fact_reasoning.rs`), with a matching
  restricted-simp certificate planner
  (`plan_explicit_discharged_implication_consequent`) and
  `lower_smart_simp_suffix_have` support, so conditional call ensures
  (`c(grown) == 1 implies owner->cap == old(owner->cap) + 1`) are usable
  by explicit simple tactics.
- `plan_restricted_simp_goal` premise availability accepts
  snapshot-bridged spellings (candidates only from listed premises).
- Certificate transports are demanded only for bridged premises consumed
  exactly (`rewrite`/`contradiction`), not those replayed through the
  bridge (`surface_replay.rs`).
- Effect footprint checks exempt a summary range keyed to a heap
  allocation live in the summary's own entry memory but absent at
  function entry — writes to a buffer a callee reallocated mid-execution,
  matched up to exact materialization
  (`c_memory_holds_live_heap_allocation_at`,
  `pointer_offsets_equal_after_exact_materialization`,
  `loads_equal_by_bounded_snapshot_match`).
- Resource-representation certification discharges implication premises
  whose antecedent the path establishes before reconciling
  (`certify_c_function_execution_path_resource_representation_uncached`).
- `examples/owned-vector/vector.click` carries the honest `grown == 1`
  closers: an explicit `frame() using { }`, normalize/intro/contradiction
  closers for the vacuous ensures, extract-based modus-ponens haves for
  the conditional ensures, and an in-progress compositional proof of the
  data-preservation forall (grow's copy forall composed with framing
  across `vector_push`).

A second, smaller casualty of the same marker fix:
`ring_buffer_pipeline.contract`'s trailing smart `simp()` relied on
launder-collapsed loads to close its ensures within budget; with honest
spellings the search exceeds its 2 s limit. Fixed in place with explicit
`have ... assumption()` closers (a prompt, bounded smart-tactic failure,
not an engine stop) — the assumption bridge chains the two call ensures
soundly.

## Remaining blocker

The inner-else finish now reaches its genuinely-new obligations and hits
an engine performance wall, not a logic gap: lowering and deciding the
data-preservation forall on this path takes 15–20 s in one call
(`have goal lowering`, `have body tactic: intro/assumption`), tripping the
6 s control budget — "a slow control tactic is a Click engine bug".
`sample` attributes the time to
`pointers_proven_equal_for_memory_resolution_with_depth`,
`pointer_offsets_equal_for_memory_resolution`,
`bitvector_terms_equal_for_memory_resolution`, and order-path queries
grinding on the path's giant nested memory spellings (each load embeds
the full memory term; two calls deep, terms embed terms). This is the
representation-cost problem already tracked by
`atomic-derivation-returns-premises-not-steps` /
`indexed-resource-algebra-avoids-pairwise-context-work`; the fix is
shared structure (interned snapshot identities on the resolution hot
path), not a larger budget.

## Reproduction

- Dropped path on master: instrument the exit drain's
  `fact_conflicts_with_assumptions` skip in
  `src/lang/click/proof/claim_proofs.rs` and verify
  `examples/owned-vector/vector.click`; the inner-else finish logs the
  skip and runs zero finish-checks, yet verification reports success.
- Engine wall on this branch: `click verify examples/owned-vector/vector.click`
  fails with the 6 s control-budget message at the forall have
  (`allocated_vector_push.contract`, statement 10); `click profile
  examples/owned-vector` shows the single-call lowering times.

The example is quarantined in `tests/examples.rs` referencing this issue.

## Structural guard landed (2026-08-15)

Proof-branch routing now distinguishes a genuine case contradiction from
explosion in an already-inconsistent routed context. Exact-negation evidence
still assigns a path to the sibling branch, but the whole-context fallback
first checks consistency and reports an explicit path-routing error when the
context is contradictory. Focused unit regressions pin both outcomes. This
closes the silent-path-drop soundness hole; it does not remove the
owned-vector quarantine because honest verification still hits the
giant-memory-term performance wall described above.

## Current-master isolation (2026-08-15)

The first failure on `baace5ab` initially looked like a slow simple proof:
a smart `step()` constructed a `SimpleProof`, then reported that independent
replay exceeded the two-second smart deadline while checking the generated
`step() using { ... }`. Replacing only that smart site with the exact printed
`step() using` disproves that diagnosis. The source-level simple step checks
normally; profiling the modified proof reports all 48 simple C steps at about
15 ms average and 128 ms maximum. Verification advances to the equivalent
smart site in the sibling branch.

The per-tactic diagnostic is therefore deadline attribution, not evidence of
a slow simple checker. Smart construction and its independent expansion
validation share the outer smart wall-clock deadline; construction consumes
most of it, and expiration is observed inside the generated step. Call this
phase **expansion validation**, distinct from ordinary **proof checking** and
from local retained-evidence verification. The diagnostic should name the
outer smart operation and its expansion-validation phase rather than imply
that the generated simple step itself exceeded a simple-tactic budget.

A separate scale blocker remains after replacing the site. The profile reaches
whole-proof **independent kernel certification**, where one
`allocated_vector_push` path takes roughly 23 seconds; about 22 seconds are in
`vector_push` verified-call ensure lowering over deeply nested memory terms.
That is the current giant-representation reproduction. Fixing or removing
per-smart-tactic expansion validation may avoid duplicate work, but it will
not by itself make owned-vector green: final kernel certification must also
stop rebuilding/traversing those giant terms.

## Acceptance criteria

- A structural guard makes silently-dropped paths impossible: each
  finish asserts that every execution path is either certified by this
  context or *proven* owned by a sibling's case set, with an error (not a
  skip) when the case fact conflicts because the context is inconsistent.
  A regression pins the guard on a laundering-style inconsistency.
- `allocated_vector_push.contract` certifies all three paths; the
  `grown == 1` finish completes within ordinary tactic budgets (no limit
  raises), including the compositional data-preservation forall.
- `examples/owned-vector` leaves quarantine and the full gate
  (`scripts/check.sh`) is green.
- An exact generated `step() using` remains an ordinary fast simple step when
  written directly; expansion-validation deadline failures are attributed to
  the enclosing smart operation and phase.
- Independent kernel certification of the completed claim avoids
  path-wide reconstruction of deeply nested memory spellings and stays below
  the ordinary per-path certification budget.
