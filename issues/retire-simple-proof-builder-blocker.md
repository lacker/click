# Retire `SimpleProofBuilder::block` in favor of `Result` propagation

## Status of the invariant

"Search succeeded but could not be expanded" is no longer a reachable
outcome for any claim proof form:

- every smart tactic's construction passes through `complete_smart_tactic`,
  which errors on a blocked or empty builder before accepting the tactic;
- every claim proof form (`auto`, `frame`, `simp`, explicit per-claim and
  grouped scripts) passes through the whole-claim certificate gate
  (`certify_claim_result` / `certify_grouped_claims_result`), which errors
  when the stitched claim-level certificate is missing, blocked, empty, or
  fails complete replay; and
- a selected-tactic expansion capture reports a blocked or empty builder as
  an expansion error (`finish_tactic_expansion_capture`), with legitimately
  empty expansions flowing through the explicit `allow_empty` outcome.

Every remaining `SimpleProofBuilder::block` call therefore surfaces as a
verification or expansion failure; none is silent. What remains is that the
guarantee is enforced by gates rather than by the type system: the
`blocker: Option<String>` field still exists, `push_step`/`push_have`
silently no-op on a blocked builder, and a new call site could in principle
be added ahead of a gate.

## Intended change

Delete the `blocker` field and the `block()` mechanism and make surface
recording failures immediate:

- `append_simple_proof_step_for_operation` and its helpers
  (`push_source_tactic`, `push_have`, the stitching appenders) return
  `Result<(), ClickError>` and propagate;
- `end_tactic_surface_scope`'s blocker forwarding, the blocker checks in
  `synthesize_surface_alternatives`, `complete_smart_tactic`, the claim
  stitchers, and `finish_tactic_expansion_capture` disappear;
- `VerifiedCTheorem::expansion_blocker` is deleted and `expanded_proof`
  becomes non-optional, since the gate already guarantees it exists.

This is a mechanical refactor across roughly thirty call sites in
`surface_replay.rs`, `claim_proofs.rs`, `cursor_execution.rs`, and
`replay_state.rs`. The one behavioral nuance to preserve or consciously
drop: a tactic-scoped builder currently starts unblocked even when the
enclosing builder is blocked, so a selected-tactic expansion can still be
produced from inside an otherwise-failed construction; with immediate
errors, the first failure aborts instead.

## Acceptance criteria

- `SimpleProofBuilder` has no `blocker` field and no `block` method; the
  compiler forces every recording failure to be handled or propagated.
- `VerifiedCTheorem::expanded_proof` is a `SimpleProof`, not an `Option`.
- The full default suite stays green, and the existing gate regressions
  (`every_claim_proof_form_carries_a_replayable_certificate`,
  `expanded_branch_certificate_uses_the_branch_entry_state`,
  `apply_construction_point_view`) keep passing.
