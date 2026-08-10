# Expansion reads retained certificates instead of probing a re-verification

Smart tactics now construct their `SimpleProof` during search and the
independent replay of that proof is the only re-execution (see the
"Construct SimpleProofSteps during smart search" change). Expansion, however,
still works by re-running full verification with the `TACTIC_EXPANSION_PROBE`
thread-local armed: `begin_tactic_expansion_capture` resets the surface
builder mid-replay when it reaches the selected tactic,
`finish_tactic_expansion_capture` harvests the builder, and whole-proof
captures abort verification through the `ClickError::expansion_complete()`
sentinel. This is capture-by-instrumentation layered on top of proofs that
are now constructed structurally, and it remains the largest source of
expansion-specific control flow:

- expansion correctness depends on a re-verification deterministically
  reaching the same proof site with the probe armed;
- the mid-replay builder reset perturbs the replay state that ordinary
  verification would have had;
- sentinel-error control flow (`expansion_complete`) threads through claim
  replay, loop planning, and forward planning;
- the deferred-tactic capture (`DeferredTacticCapture`,
  `deferred_expansion_path_choices`) is consulted at roughly twenty
  finalization sites in `claim_proofs.rs`.

## Intended design

Verification retains the expansion of every proof site as a value, and
expansion becomes: verify once (no probe), look up, print.

- `complete_smart_tactic` already holds each smart tactic's `SimpleProof`;
  retain it keyed by `(ProofSite, source_index)` in a `RetainedExpansions`
  store threaded through the claim-proof results (a return value, not a
  thread-local).
- Deferred post-execution smart tactics retain the surface tactic recorded by
  `record_post_execution_surface_tactic` at finalization, keyed the same way.
- Whole-proof sites retain the final `SimpleProofBuilder` steps (these are now
  the structural accumulation of the constructed proof, not an
  instrumentation artifact); loop phases already retain per-phase
  `SimpleProof`s in `LoopProofCertificates` and should feed the same store.
- A tactic replayed under several claims (or under several enclosing C branch
  paths) retains one entry per replay; the current in-flight
  "selected tactic expands differently across proof obligations" check
  becomes an expansion-time comparison of the retained entries, and the
  sibling-branch merge becomes `synthesize_surface_paths` over the retained
  per-path entries with their recorded `SurfacePathChoice`s.
- `verification.rs` currently narrows which functions are verified by reading
  `active_c0_tactic_expansion_request()` from the probe; pass the expansion
  target down as an explicit argument instead.

Then delete: `TACTIC_EXPANSION_PROBE`, `begin/finish_tactic_expansion_capture`,
`record_proof_site_tactic_expansion`, `finish_proof_site_expansion_capture`,
`selected_tactic_index_for_site`, `active_c0_tactic_expansion_request`,
`ClickError::expansion_complete`, `SUPPRESS_TACTIC_EXPANSION_CAPTURE`,
`DeferredTacticCapture`, and `deferred_expansion_path_choices`.

With the probe gone, `SimpleProofBuilder` no longer needs to live inside
`TacticReplayState` for capture's benefit; a follow-up can pass it explicitly
where proofs are built and drop the remaining ambient threading
(`lowering_planned_transition`, capture-driven builder resets).

## Constraints learned during the search-construction migration

Two invariants matter for anything that touches construction, and regression
coverage for both lives in the ordinary suite:

- Premises must be spelled against the replay-visible fact set
  (`SimpleProofBuilder::certificate_facts`), not the planning executor's
  automatically transported facts; otherwise a later step can name a spelling
  its own replay has pruned
  (`expanded_branch_certificate_uses_the_branch_entry_state`).
- Construction must see program points exactly as they stood before the
  current statement's entry recordings; a fresh or overwritten entry snapshot
  lets a premise anchor at a point whose replay-time state lowers differently
  (`resource_neutral_callee_preserves_callers_allocation_resource`).

## Behavior note

Partial-tactic expansion today aborts the claim replay right after the
selected tactic via the sentinel error. Retained-value expansion runs the
verification to completion instead. The suffix after the selected tactic and
the remaining claims of that function do run; the cross-function narrowing
must be kept (as the explicit argument above) so expansion latency stays
proportional to the selected function.

## Acceptance criteria

- `click expand` output is byte-identical to today's on the existing
  expansion test corpus (`lang::click::expansion::tests`).
- No thread-local participates in expansion; `verify_c0_sources` has no
  expansion-dependent behavior beyond the explicit function-narrowing
  argument.
- A tactic that expands differently across proof obligations still fails with
  the existing diagnostic, now produced by comparing retained entries.
- The deferred-capture consultation sites in `claim_proofs.rs` are gone.
