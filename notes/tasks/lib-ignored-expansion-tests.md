# lib: 7 #[ignore] expansion-era tests

Status: diagnosed — 0 un-ignored, 6 stay here, 1 moved to the parked family
Claimed:

Scope: 7 `#[ignore]` lib tests from the expansion era. Retest against
current master (the 2026-07-30 certifier/expansion work moved a lot);
un-ignore what passes, diagnose what doesn't into this file.

Repro: `cargo nextest run --lib --run-ignored ignored-only --no-fail-fast`.

## Retest result (2026-07-30)

All 7 still fail. **None is slow** — the whole set runs in 0.15 s, so
there is no timing debt here; the old "run with --ignored" reasons hid
fast, ordinary failures.

The 2026-07-30 certifier work moved **none** of them: `CLICK_DISABLE_CERT_ARMS=1`
and `CLICK_DISABLE_DECIDE_MEMO=1` both reproduce all 7 failures identically.
These are older debts, not fallout from the new arms/memo.

Every one carried the same blanket reason, "item-7 nested snapshot
spellings (store-provenance debt)". That label was wrong for 6 of the 7.
Reasons have been rewritten in place to match the real cause.

| test | verdict | family |
| --- | --- | --- |
| expands_nested_branch_tactic_by_source_location | still fails | premise over-inclusion |
| execute_rest_return_certificate_omits_unused_ambient_facts | still fails | premise over-inclusion |
| expands_grouped_immutable_read_with_multiple_claim_successors | still fails | premise under-inclusion |
| execute_step_expands_call_assign_fact_from_internal_snapshot | still fails | premise under-inclusion |
| expansion_preserves_unfolded_resource_and_predicate_fact_spellings | still fails | aggregate separation spelling |
| verifies_opaque_predicate_from_requirement | still fails | predicate opacity vs. lowering |
| verifies_old_memory_loop_invariant | still fails | store-provenance (PARKED — moved) |

## Family 1: certificate-premise policy (4 tests, one root)

These four are the same knob set two different wrong ways, and they
contradict each other, so no re-baselining fixes the pair. The selection
site is `src/lang/click/proof.rs` ~13795-13871, in the
`ProofTactic::CertifiedStatementStep` arm of `record_surface_replay_tactic`.
A fact becomes a `step using` premise when it is `selected_by_derivation`,
or `non_reconstructible_separation`, or:

```rust
let claim_transition_context = matches!(fact, Proposition::ConditionIs(_, _));
```

**Over-inclusion** — that last line keeps *every* ambient `ConditionIs`
fact unconditionally, whether or not a derivation needed it:
- `execute_rest_return_certificate_omits_unused_ambient_facts` asserts the
  certificate is `Step`; it is `StepUsing([x < 100])` — the `requires x < 100`
  precondition, unused by the goal `result == x`. This test is the direct
  guard for the bug; do not re-baseline it.
- `expands_nested_branch_tactic_by_source_location` expects the nested
  then-branch to expand to a bare `step();`; it expands to
  `step using { fact x == x; }` — the proof-branch hypothesis. Location
  targeting, indentation and the `execute_rest` count are all correct, and
  the result re-verifies; only the premise is spurious.

**Under-inclusion** — memory/resource facts are dropped whenever they are
reconstructible from the resource state, so certificates that used to carry
premises are now bare:
- `expands_grouped_immutable_read_with_multiple_claim_successors` expects
  `step using {`; gets `step();`. Verified by probe: with that one assert
  neutralized the test **passes**, i.e. the bare `step()` really does
  re-verify every grouped claim. Only the shape string is stale.
- `execute_step_expands_call_assign_fact_from_internal_snapshot` expects
  `step using {`; the caller's `execute_step()` expands to `step();` with no
  premise at all. Its only assert is that shape, and the test exists to check
  the callee's *internal snapshot* fact gets carried — re-baselining to
  `step();` would delete the point of the test rather than fix it.

Not attempted: the fix is a coherent premise-selection policy in `proof.rs`,
outside this task's lane (test modules only). Worth doing as one change —
patching either direction alone will flip the other pair red.

## Family 2: aggregate separation spelling (1 test)

`expansion_preserves_unfolded_resource_and_predicate_fact_spellings`.
`unfold(owned_box(owner))` decomposes
`separate(memory(object(owner)), memory((owner->data)[0..owner->cap]))`
into six pairwise field separations (`owner->len` vs `owner->cap`,
`owner->len` vs the data range, ...). Semantically that is equal-or-stronger,
but the aggregate `object(owner)` spelling never reaches the emitted premises,
so the assert for the one-line aggregate form fails. The other two asserts in
the test are satisfied — note the `terminated_at` one passes only incidentally,
matching the resource *declaration* echoed in the expansion rather than the
step-using block, so it is not really testing what it reads as.

`object(owner)` is a documented canonical struct spelling (notes/conventions.md),
so the decomposition is a genuine spelling regression rather than a stale
expectation — but it is a printing/re-folding concern, not soundness.

## Family 3: predicate opacity vs. lowering (1 test)

`verifies_opaque_predicate_from_requirement`. Fails at contract certification,
before any tactic: "exact symbolic execution produced no valid paths". The
predicate `sorted_pair(p) { p[0] <= p[1] }` is carried `requires` -> `ensures`
and never unfolded, but it still lowers to its body, so the `p[0]`/`p[1]` loads
need loadability the contract never states; every path is infeasible and all
get pruned.

Confirmed by probe: adding `requires loadable(p, 8);` makes it pass
immediately. The passing sibling `unfolds_predicate_requirement_to_prove_consequence`
differs from it by exactly that line.

Left ignored deliberately. Adding the precondition to the test would make it
green while removing the property it names — whether an *opaque* predicate
should owe its body's memory obligations is a Surface Click semantics question,
and conventions.md puts those on the owner.

## Done / not done

- 0 un-ignored (none passes; none could be made to pass without weakening).
- All 7 `#[ignore]` reasons rewritten from the blanket wrong label to the real
  cause, each with a pointer back here.
- `verifies_old_memory_loop_invariant` handed to
  `store-provenance-family.md` and is no longer tracked in this file.
