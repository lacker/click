# proof.rs panic sites reachable from user input

Status: done (2026-07-30)
Claimed: claude/proof-panics, 2026-07-30

Scope (design-review honorable mention): 35 panic!/unreachable! sites
in src/lang/click/proof.rs are reachable from user-dependent data
(e.g. the old proof.rs:20043) and turn diagnosable proof bugs into
crashes. Convert the reachable ones to ClickError diagnostics.

## Result

Enumerated 94 `panic!` / `unreachable!` / `.expect(` sites; 16 are in
the `#[cfg(test)]` module (lines 951-1190) and are out of scope, leaving
**78 production sites**. Every one was classified by reading its guard.

- **7 converted** to `ClickError` (or to a propagated `Result`).
- **71 left** as genuine internal invariants.
- **0 blocked**: no conversion needed a change to what gets accepted.
- **6 mdtests added**, covering the diagnostics that stand in front of
  the assertion-heavy paths (see "Tests" below).

The headline finding is that the design review's estimate does not hold
up. Its cited example, the old `proof.rs:20043`
(`record_observed_composite_surface_facts`'s
`definition.composite_body().expect(...)`, now line 20243), is a false
positive: both call sites establish `composite_body().is_some()` first —
one through `composite_resource_law_definition`, the other through a
`let Some(composite_body) = ... else { return Ok(()) }`. That pattern
repeated across the file. The 71 "left" sites are not judgement calls;
each is guarded by a check within a few lines, by a `match`/`find` that
just selected the variant being re-destructured, or by a constructor
whose only producer is the parser.

Empirical confirmation: 43 adversarial sidecars (malformed proof
scripts, resource laws on the wrong resource family, control-flow
tactics in pure scopes, tactics at impossible frontiers, nested
composites, out-of-range regions) were run through `click-verify`.
**Every one produced a clean `ClickError`; none panicked.**

## Converted (7)

| Line (pre-change) | Site | Why it is not an invariant |
| --- | --- | --- |
| 2620 | `prove_claim_by_auto`, `.expect("auto should attempt at least one certificate candidate")` | Depends on `bounded_execution_tactic_candidates` / `auto_loop_verification_tactic_candidates` being non-empty — a fact about two functions 19k lines away, not a local guard. Now names the claim. |
| 3048 | `finish_tactic_expansion_capture`, `.expect("... requires an active probe")` | Asserts thread-local `TACTIC_EXPANSION_PROBE` state established by a different call. Now returns a real `ClickError` when the probe is gone. |
| 5472 | `verify_execution_proofs_forward`, `.expect("effect certificate site should name a structural item")` | The `item_index` is plumbed through `LoopPreservationProofResult` from a `.find()` in a different function; the two `.find()` calls only agree by convention. Now names the loop and item index. |
| 8861 | `prove_pure_proposition_case_at_point`, `.map(\|_\| unreachable!("stalled premise should still fail"))` | Asserts that re-running `lower_point_proposition_with_values` with unchanged inputs fails again. True today, but it is a determinism assumption about a large lowering routine, not a guard. Now falls back to a message. |
| 18476 | `execute_concrete_loop_head_step`, `.expect("source loop should have a body entry")` | `loop_index` is resolved on a different path from the `SourceLayout` that owns `loop_bodies`. Now names the claim, tactic, and loop. |
| 19804 | `split_next_source_operation`, `.expect("flattening a C statement sequence should succeed")` | `flatten_top_level_sequence` returns `Result`; the enclosing function already returns `Result<_, String>`, so the `?` is free. Propagates instead. |
| 21175 | `fold_composite_resources_on_outcome`, `unreachable!("batch and sequential resource consumption disagreed")` | The only site in the file that asserts **agreement between two separately implemented algorithms** (`ResourceContext::without_facts` in batch vs. repeated `without_fact`). A kernel-side divergence would crash the tool. Now reports `fold(...)` could not consume the body as a whole. |

Behaviour on valid input is unchanged: all seven only fire where the
process previously aborted.

## Left as genuine invariants (71)

Grouped by the reason, with representative line numbers.

**Re-destructuring what a `match`/`find`/guard just selected (30 sites).**
1371, 1558 (`find` matched only `If | Advance`); 5131 (guarded by
`!matches!(policy, None)`); 8145, 9099, 10319, 11670, 11733, 14789,
15305, 15327, 15579, 15827, 16284, 16883, 16893, 16912, 16934, 17939,
18375, 19211 (inside `if let Some(...) = match &outcome { Normal|Return
=> Some, UB|RuntimeError => None }`), plus the `let ... else
unreachable!("tactic class and variant must agree")` family. 9099 was
checked exhaustively: all twelve tactics admitted by the outer arm are
handled by the inner match.

**Locally guarded `Option`/length checks (14 sites).**
8283 (`Err(_) if prelowered_goal.is_some()` match guard); 8764, 8903,
8911 (preceded by `if goal.is_none() { goal = Some(...) }`); 8999
(`prepared_derivation_lowering_facts` is set in the same `if let
Derive|Calculate` that this arm matches); 13135 (guarded by the same
`exact_fact_is_available` call); 17224 (`completed.len() == 1`); 17382
(guarded by the matching `.any()`); 17884, 17936 (`.facts().last()`
after `unchecked_with_fact`, which is a plain `push`); 18261, 18452,
19119 (an emptiness check returns `Err` immediately above); 19021,
19024 (`direct_transition` is `Some` only via `certified_replay.map`);
18263 (`BranchStepPolicy::Explore` is only passed with
`Some(take_then)`).

**Parser-enforced type correspondence (4 sites).**
5869, 6211, 6311 (`StructuralItem::proposition()`): `parse_region_proof_items`
is the only producer and pairs `Invariant`/`Assert` with
`StructuralItemClaim::Proposition`, `immutable`/`mutable`/`step` with
`Effect`. 17936/17939 similarly: `lower_resource_clause_with_values`
maps `ResourceKind::Composite` to `CResource::Composite` unconditionally.

**Callers establish the precondition (8 sites).**
20243, 20866, 21056 (`composite_body()`): every caller either goes
through `composite_resource_law_definition`, which returns
`Err("... expects composite resource `{name}` to have a body")`, or
through a `let Some(composite_body) = ... else { return Ok(()) }`.
This is the design review's cited example and it does not reproduce.
16288, 16447, 17263, 19573 (`replay.execution()`): `execution()` is
`Some` exactly at `ProofExecutionPoint::FunctionExit`, and each site is
behind `require_function_exit` or an explicit
`is_at_function_exit` check. 17757 (`SourceLayout::statement` of a node
that `loop_statement` returned; `visit` inserts both maps together).

**Cross-module contracts verified by reading the callee (11 sites).**
3785: `substitute_c_fragment_as_contract` can only fail on a
non-C-fragment substitution, and the call passes an empty map.
5075, 5137, 8105: `prove_c_condition_fact_transport{,_direct}` has
exactly one `Some(...)` return and it is `Proposition::Implies`.
12956, 13021, 13073: surface loadability obligations are only recorded
by `record_surface_loadability_obligation`, which always builds a
`Proposition::CMemoryLoadable`.
14868: `surface_simp_plan_proof`'s only success returns are
`Proof::Script`. 9949, 10121, 10234, 10731, 15157, 15216, 16315:
`TacticCertificate::from_proof_tactics` / `ProofReplayPlan::from_planned_tactics`
on tactic lists built here from `Assumption`, `Normalize`,
`ExactPropositionDerivation`, `TransportUsing`, `ApplyTheoremUsing`,
`CertifiedFrame`, `UnfoldPredicate`, or the empty list — every one
`TacticClass::Simple` and (where required) surface-expressible.
10227: `replay_fact_transport_at_outcome` returns `TransportUsing` on
both of its arms.

**Control-flow tactics are expanded before replay (2 sites).**
9103, 16883. `expand_proof_if_cases` / `build_internal_proof_at` split
at the first `If`/`Advance` and recurse into both the branch bodies and
the suffix, so no linear segment can contain one. Verified empirically
too: `if` nested in a `have`, `if` nested inside an `advance` body
inside an `if`, and `advance` in a pure `have` scope all reach an
ordinary diagnostic (the last is now `mdtests/pure_have_rejects_advance.md`).

## Deliberately not converted, worth knowing

- `claims[0]` in the `ProofTactic::Frame` arm (~16382, ~16426) is an
  index panic rather than a listed site, so it was out of scope for the
  grep. `claims` is non-empty on every path reached today, but it is
  not checked at the site.
- `flatten_top_level_sequence` returns `Result<(), String>` and never
  produces `Err`. The dead error arm is now propagated rather than
  asserted, but the signature could be simplified to `()`.
- The `unreachable!("tactic class and variant must agree")` family
  lives in `src/lang/click.rs`, outside this task's lane.

## Tests

Six new mdtests, each exercising a diagnostic that stands between a
malformed script and one of the classified assertion paths:

- `mdtests/pure_have_rejects_advance.md`
- `mdtests/unfold_rejects_bodyless_resource.md`
- `mdtests/observe_rejects_unknown_resource.md`
- `mdtests/apply_loop_summary_rejects_wrong_point.md`
- `mdtests/transport_rejects_function_entry.md`
- `mdtests/witness_rejects_before_function_exit.md`

None of the seven converted sites could be triggered from Click source:
each is reachable only if an internal contract is already broken, which
is exactly why they are now diagnostics instead of crashes. No mdtest
asserts them.

## Repro

```
grep -n 'panic!\|unreachable!\|\.expect(' src/lang/click/proof.rs
cargo nextest run --lib          # 465 passed
cargo test --test mdtests        # ok
cargo test --test examples       # ok
```
