# One-gateway check: no bypass around TacticCertificate replay

Status: done (audit complete 2026-07-30) — VERDICT: bypasses found
Claimed:

Scope: one bounded code audit (reading task, not a refactor) verifying
that every smart-tactic success commits through TacticCertificate
replay with no bypass path. Follows from the settled invariant that
TacticCertificate is the smart/simple boundary.

Where to look: src/lang/click/proof.rs — replay_smart_plan,
lower_internal_plan_to_surface_certificate, replay_internal_plan, and
every call site of the internal-plan executor; confirm each smart
acceptance path routes through certificate replay and that no
error-recovery or legacy arm accepts an internal plan directly.

Done when: a short written finding (extend this file) either confirming
the single gateway or listing concrete bypass sites as new tasks.

## Verdict

There is **no single gateway**. Smart acceptance splits into two
worlds, and only one of them is gated.

- **Mid-execution smart tactics** (frontier not at function exit) all
  funnel through `replay_smart_plan` (proof.rs:17320), which is a
  genuine gateway: `lower_internal_plan_to_surface_certificate` builds
  a `TacticCertificate` and `verify_surface_certificate` replays it
  from the *original* context; both errors are `?`-propagated and the
  returned context is the certificate's, not the plan's.
- **At-function-exit smart tactics** are deferred into
  `TacticReplayState::post_execution_tactics` and discharged in a
  completely separate drain loop inside `verify_execution_proof`
  (proof.rs:~9846-10970). In that world the certificate gate holds only
  when `replay.grouped_contract` is true. For per-claim proofs
  (`grouped_contract == false`) three arms accept first and certify
  best-effort; a certification failure is downgraded to an
  *expansion blocker* and the claim stays closed.

The bypasses are **not obviously unsound** — the claims are still
kernel-checked by `check_function_claim_by_simp` /
`check_function_claim_with_existence_tactics` / `prove_have_at_point`.
What is violated is the settled invariant that a smart success must be
expressible as, and replay through, a surface certificate. In practice
these are smart successes that no surface certificate reproduces.

## Acceptance paths enumerated (and how each was checked)

Smart list taken from `ProofTactic::class()` (src/lang/click.rs:1143+):
`ApplyTheorem`, `Transport`, `ExecuteStep`, `ExecuteThenStep`,
`ExecuteElseStep`, `ExecuteRest`, `ExecuteUntil`, `BoundedExecute`,
`ContextualFrame` (= surface `frame`), `Simp`; plus `SmartTactic::{Auto,
Frame, Simp}` as whole-proof spellings.

GATED — verified by reading, all in `replay_linear_tactics`:

| tactic | site | shape |
| --- | --- | --- |
| `Transport` (pre-exit) | proof.rs:15091 `if let` guard | plan `TransportUsing` -> `replay_smart_plan` |
| `ApplyTheorem` (pre-exit) | proof.rs:15208 `if let` guard | plan `ApplyTheoremUsing` -> `replay_smart_plan` |
| `ExecuteStep` | proof.rs:15944 | throwaway `planning_replay`/`planning_state`, only `planned_tactics` survive -> `replay_smart_plan` |
| `ExecuteThenStep` | proof.rs:16004 | same shape |
| `ExecuteElseStep` | proof.rs:16063 | same shape |
| `ExecuteRest` | proof.rs:16122 | same shape |
| `ExecuteUntil` | proof.rs:16175 | same shape |
| `BoundedExecute` | proof.rs:16237 | same shape |
| `ContextualFrame` | proof.rs:16291 | plan `CertifiedFrame` -> `replay_smart_plan` |
| smart `have` w/ `apply` (pre-exit) | proof.rs:16862 | `pure_goal_certificate_gateway` + `verify_surface_certificate` |
| smart `have` w/ `simp` suffix (pre-exit) | proof.rs:16833 | `surface_smart_have_certificate` -> same gateway |

Other gated entry points (read, no bypass found):

- `prove_claims_by_grouped_auto` (proof.rs:9496): proves, then
  `expanded_proof_certificate()` (fails if any expansion blocker) and
  re-runs `prove_claims_by_grouped_tactics` on the certificate.
- `prove_claim_by_auto` (proof.rs:2524) -> `certify_auto_claim_result`
  (proof.rs:2628): same plan/expand/replay round trip for both the
  loop-verification and bounded-execution candidate families.
- Loop-region proofs (proof.rs:6393, 6651): build a merged
  `TacticCertificate` per case path and re-run it through
  `execute_internal_proof` ("preservation certificate failed ordinary
  replay").
- `verify_structural_effect_proof` (proof.rs:6538): certificate first,
  then replay.
- Pure-theorem goals: `pure_goal_certificate_gateway` (proof.rs:635) —
  plan, re-validate as a certificate, replay, propagate both errors.
- Post-execution smart `apply` (proof.rs:9933) and post-execution smart
  `transport` (proof.rs:10197) DO certify-then-replay even in the
  ungrouped case (`replay_outcome_apply_certificate` /
  the second `replay_fact_transport_at_outcome` on a cloned fact set).
- Post-execution smart `have` whose proof is `simp`-suffixed
  (proof.rs:10037): lowers to `Have(..., Script([unfold*, <simple>]))`,
  builds the certificate, replays via `prove_have_at_point`, and
  rejects if the replayed fact differs.
- Grouped post-execution `simp` (proof.rs:10885): a failure of
  `certify_grouped_outcome_simp_transition` is `return Err(error)`.
- `ProofTactic::CertifiedAlternatives` calls `replay_internal_plan`
  directly (proof.rs:15897) — **not** a bypass:
  `validate_certificate_tactics` (click.rs:970) explicitly rejects
  `CertifiedAlternatives` inside a `TacticCertificate`, so an internal
  plan cannot be laundered into a certificate through it. Likewise
  `SimpleTactic::is_surface_expressible` (click.rs:1128) keeps the
  `Certified*` simple tactics out of certificates.

## Bypasses (do NOT fix here — each changes what gets accepted)

All three live in the ungrouped (per-claim) post-execution drain, i.e.
`prove_claim_by_tactics` (proof.rs:9259) with `grouped_contract: false`.
All three are reachable from an ordinary user proof script: any
per-claim `by { ... simp; }` (or `by simp;`, which
`prove_claim_by_simp` at proof.rs:2721 expands to
`[ExecuteRest, Simp]` and — unlike `by auto;` — does **not** run
`certify_auto_claim_result`).

### BYPASS-A — ungrouped post-execution `simp` accepts without a certificate

- Site: `src/lang/click/proof.rs:10820-10834` (the `match surface_tactic`
  after `check_function_claim_by_simp` succeeded).
- `closed_claims[claim_index] = true` is set at proof.rs:10704 on the
  `Ok(())` of the ambient simp check, *before* `certify_outcome_simp`
  (proof.rs:13320) runs. On `Err(message)` the only effect is
  `surface_closer_blockers[claim_index].get_or_insert(message)`, which
  is consumed at proof.rs:11152 solely to set `expansion_blocker` on the
  `VerifiedCTheorem`. Verification returns `Ok`.
- This includes the case where the certificate WAS built and its replay
  failed: `certify_outcome_simp_have` raises "smart `simp` certificate
  failed replay" (proof.rs:13325) from `prove_have_at_point`, and that
  error lands in the same swallowing `Err` arm. That is literally
  "if replay fails, accept anyway".
- User-exploitable: yes. Every observed instance is a hand-written
  per-claim script.

### BYPASS-A' — ungrouped post-execution `simp` with existential tactics

- Site: `src/lang/click/proof.rs:10835-10842` (the `else` of
  `existence_tactics.is_empty()`).
- With a pending `witness`/`choose`, the claim is closed by
  `check_function_claim_with_existence_tactics` and the code
  unconditionally records the blocker "surface `simp` lowering with
  existential tactics is not implemented". No certificate is ever
  attempted. Accepted anyway.
- User-exploitable: yes.

### BYPASS-B — post-execution `have` runs a smart proof script directly

- Site: `src/lang/click/proof.rs:10164-10183` (the `else` branch of
  `smart_simp_unfold_prefix(&have.proof)`).
- `smart_simp_unfold_prefix` (proof.rs:14650) returns `Some` only when
  the have's script is `[UnfoldPredicate*, Simp]`. Any other script
  falls through to `prove_have_at_point(have, ...)` with **no**
  certificate lowering, and `ProofTactic::Have(have.clone())` is
  recorded verbatim as the surface tactic.
- If that script contains a Smart tactic (`simp` after
  `witness`/`choose`/`advance`, or `apply`), a smart success is accepted
  and a non-certificate tactic is emitted into the expansion. Compare
  the mid-execution `have` at proof.rs:16862, which *does* route smart
  `apply` through `surface_smart_apply_have_certificate` — the
  asymmetry is the bug.
- User-exploitable: yes.

## Evidence

Method: temporary `CLICK_AUDIT_GATEWAY=<logfile>` instrumentation at
each candidate site (append-to-file, because the examples/mdtests
harnesses run child processes with piped stderr). Positive `LIVE-*`
counters were added at the same sites first, to prove the sites are
exercised at all rather than reading zeros off dead code.
**Instrumentation was stripped before committing; src/ is unchanged.**

- `cargo nextest run --lib --bins`: 278 gateway events, 5 BYPASS-A hits
  in 4 passing tests — `unfolds_predicate_goal_to_prove_compare_swap_sorted`,
  `unfolds_predicate_requirement_to_prove_consequence`,
  `unfolds_general_sorted_predicate`,
  `loop_phase_proofs_can_unfold_invariant_predicates`.
- `cargo test --test mdtests`: 599 gateway events — 345 certified
  (`LIVE-A`), **39 bypass hits**: 30x BYPASS-A across 21 distinct
  claims, 6x BYPASS-A', 3x BYPASS-B. All in passing mdtests.
  Distinct BYPASS-A claims: `advance_selected_pointer.ensures_0`,
  `bubble_sort3_loop_permutation.permutation`,
  `byte_slice_facts.current_equals_old`,
  `compare_swap2_permutation.pair_permutation`,
  `compare_swap2_sorted_predicate.sorted`,
  `cstr_stdlib.{bounded_has_terminator, exact_has_terminator,
  exact_length_nonnegative, exact_prefix_has_no_null}`,
  `identity_permutation.same_multiset`,
  `identity_two_arrays.unfolded_requirement`,
  `increment_value.predicate_value`,
  `keep_first_change_second.first_cell_preserved`,
  `loop_explicit_initialize_and_preserve.ensures_0`,
  `loop_sorted_range_invariant.still_sorted`,
  `loop_stdlib_permutation_invariant.permutation_after_loop`,
  `sort3_permutation.permutation`,
  `sort3_permutation_predicate.permutation`,
  `sorted_pair_unfold_requirement.consequence`,
  `sorted_predicate.still_sorted`,
  `theorem_apply_identity.ensures_0`.
  BYPASS-A' claims: `byte_slice_range_predicates.opened_contains`,
  `choose_requirement.found_again_by_{index,label}`,
  `identity.result_matches_witness`,
  `plain_cstr.exposes_ghost_length`, `witness_zero.found_zero`.
  BYPASS-B scripts: `identity.contract`
  (`[choose k, witness j = k, simp]` and `[witness j = result, simp]`)
  and `joined_increment.ensures_1` (`[advance(...){simp}, simp]`).
- `cargo test --test examples`: 105 gateway events, **0 bypass hits**.
  The examples corpus is entirely on the gated (grouped / auto) paths.

The dominant BYPASS-A causes, from the swallowed messages:
"smart `simp` surface goal lowered to a different kernel proposition"
(proof.rs:12941), "expressible path facts do not replay the
postcondition derivation" (proof.rs:12748), "planned `simp` context
premise is not an available source fact" (proof.rs:12315). All three
cluster around `unfold(...)`-active goals and predicate-valued
postconditions — the surface spelling of the goal cannot be recovered
once a predicate has been unfolded.

## Suggested follow-up tasks (not done here)

1. **Gate the ungrouped post-execution `simp`** — make
   `surface_closer_blockers` a hard error like the grouped arm at
   proof.rs:10885, i.e. re-open `closed_claims[claim_index]` when
   certification fails. This is a semantics change: the 21 mdtest
   claims listed above would start failing until the underlying
   lowering gaps (unfold-active goals, predicate postconditions,
   existential closers) are fixed. Sequence it as: fix lowering gaps
   first, then flip the gate.
2. **Certify the existential-closer path** — implement surface `simp`
   lowering with `witness`/`choose` so BYPASS-A' has a certificate to
   produce instead of an unconditional blocker.
3. **Lower post-execution `have` scripts** — extend
   `smart_simp_unfold_prefix` / add a post-execution analogue of
   `surface_smart_apply_have_certificate` so a `have` at function exit
   is certificate-gated the same way it is mid-execution.
4. **Add a debug assertion / test** that no `VerifiedCTheorem` with a
   Smart tactic in `expanded_proof_tactics` is ever returned, and that
   an `expansion_blocker` on a smart closer is a verification error —
   so this class of bypass cannot silently reappear.

## What could NOT be verified

- **Soundness impact.** This audit checked the *gateway invariant*, not
  whether the ambient closers (`check_function_claim_by_simp`,
  `check_function_claim_with_existence_tactics`) are themselves sound.
  They do run kernel checks, so the bypassed claims are not unchecked —
  but I did not verify that the ambient check is exactly as strong as
  the certificate replay it is standing in for. If it is weaker in any
  respect, BYPASS-A is a soundness hole rather than an invariant hole.
  That needs its own task.
- **Negative reachability of a crafted exploit.** I did not construct a
  minimal `.click` repro that closes a claim the certificate path would
  reject. The evidence is observational (39 existing corpus hits), not
  adversarial.
- **The `src/kernel/*` side.** Out of bounds for this task (another
  agent was editing it), so I did not check whether any kernel-level
  acceptance path can be reached without going through
  `src/lang/click/proof.rs` at all.
- **click-expand / click-audit end-to-end behaviour** on the bypassed
  claims. Expansion should refuse them (the blocker is set), but I did
  not run click-expand over the 21 affected mdtests to confirm the
  refusal is user-visible rather than silently emitting the source
  script.
- **Exhaustiveness below `have` bodies.** I traced the top-level and
  post-execution tactic loops exhaustively, and `have`/`if`/`advance`
  bodies at the sites named above, but did not enumerate every nested
  `have`-inside-`if`-inside-`advance` combination in the region-proof
  world.
