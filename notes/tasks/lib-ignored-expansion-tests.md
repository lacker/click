# lib: 7 #[ignore] expansion-era tests

Status: 5 un-ignored (4 by the premise-policy fix), 1 stays here, 1 moved
to the parked family
Claimed: worktree-agent-a00f20ca6b0de59b8 + 2026-07-30

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
| verifies_opaque_predicate_from_requirement | **PASSES (un-ignored 2026-07-30)** | fixed by the definedness rule |
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

**Fixed 2026-07-30 on `worktree-agent-a00f20ca6b0de59b8`. All four now pass
and are un-ignored.** See "The premise policy" below.

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


## Update 2026-07-30 (evening): one of the seven is fixed

`verifies_opaque_predicate_from_requirement` now passes and is
un-ignored. Owner ruling: a predicate that reads memory cannot be true
unless that memory is readable, so an assumed `requires` carries its own
definedness — `loadable` is a fact about memory safety and bounds
(docs/intermediate/permissions.md), not an authority, so assuming it
alongside an assumed requirement manufactures no permission.

Implemented in `contract entry assumptions` (src/kernel/api.rs): an
obligation arising from lowering a `requires` is assumed rather than
proven **when it is `is_assumable()`** — the flag the kernel already used
to separate definedness obligations from genuine verification
conditions. Non-assumable obligations still have to be discharged.

The dual direction is unchanged and now pinned by two tests:
`heap_dependent_ensures_still_owes_its_loads` and
`call_site_owes_the_definedness_of_a_heap_dependent_precondition`. If
either starts passing, the assumption side has become a way to
manufacture readability out of nothing.

Remaining ignored: 6 (four premise-selection policy, one aggregate
separation spelling, one store-provenance).


## The premise policy (2026-07-30, branch worktree-agent-a00f20ca6b0de59b8)

All four family-1 tests are fixed and un-ignored. Two commits:

1. `Record which ambient conditions a statement certificate consumed`
2. `Spell the permissions the resource projection cannot reconstruct`

The policy a `CertifiedStatementStep` certificate now implements — a
certificate carries exactly what the derivation consumed:

- the prerequisite derivations' context premises and the transition's
  exact premises (unchanged);
- every ambient **permission** fact the resource projection cannot
  reproduce — separations *and* loadability. One the projection
  reproduces is reconstructed by the replay for itself and stays out;
- the ambient **conditions**, but only when this transition's execution
  can have consulted them.

### Why the conditions need a flag rather than a filter

The old `claim_transition_context` blanket kept every ambient
`ConditionIs`. It cannot simply be deleted: 35 lib tests go red. The
reason is that the information is *destroyed* before selection runs.
Planning executes with the whole ambient context, so a condition it
relied on leaves no trace in the transition — the undefined-behaviour
path it excluded is simply absent, and the segment lookup it bounded
simply succeeded. Neither the theorem, the path facts, nor the
obligations distinguish `requires x < 100` (never touched by `return x;`)
from the loop invariant that ruled out an overflow.

So the decision is made in `certified_statement_transitions`, where the
statement is still in hand, and recorded on the transition as
`consults_conditions`. It is true unless the statement only moves a
variable or a constant **and** the context cannot turn a condition into a
memory conclusion (no resources, no non-condition facts). Both halves are
needed — see the dead ends.

Second half of the over-inclusion fix: the theorem-premises loop in
`certified_transitions_from_execution` was manufacturing an identity
derivation (`x < 100` from `x < 100`) for any ambient condition the
theorem carried, which advertised an untouched precondition as a
prerequisite. It now skips premises that are already exactly available.

### Dead ends (all measured, none kept)

- **Deleting the blanket alone**: 35 lib failures, split between
  overflow-condition selection and segment/loadability lookups.
- **`defer_non_exact_condition_reasoning` for Planning** (so generation
  sees the same obligations replay will): breaks the smart tactics
  themselves — `execute_rest` starts reporting signed overflow, because
  planning can no longer prove the safe path.
- **Path facts as exact premises**: the safe path's own facts are what
  selected it, so this looks right, but planning records nothing for a
  condition it discharged; measured to change no test either way, so it
  was dropped for minimality.
- **Re-executing the statement with the conditions withheld** (the direct
  empirical test): correct answers, unaffordable. It made
  `expanded_read_step_keeps_named_range_separation_premises` go from
  0.22 s to over 60 s, because withholding facts makes the execution
  split where it did not before. Bounding the probe budget did not
  recover the time.
- **Selecting conditions by resource-projection dependency**: does not
  reach the failures, which are resource *containment* during execution
  (`owns p[i..i+1]` from `owns p[0..n]`), not the
  `observable_facts_assuming_valid` projection.
- **`statement_consults_conditions` alone, without the memory-context
  half**: `mdtests/forall_array_segment.md` regresses. Its body is
  `return n;` — a pure scalar move — but the post-execution `simp` has to
  spell `loadable(p + k, 4)`, which needs the `0 <= k < n <= 3` bounds.
  A statement that cannot consult a condition itself can still sit in a
  context that turns one into a memory conclusion.

### Latent bug found and NOT fixed here

`condition_polarity_equivalent` (proof.rs) compares
`canonical_order_condition(..) == canonical_order_condition(..)`. Only
comparisons have a canonical order form, so **two conditions that both
lack one compare equal** — `None == None`. That makes
`exact_fact_is_available` answer yes for any non-comparison condition
(an overflow check, `PointerOffsetEqual`, a constant) whenever the
available set holds any other non-comparison condition.

Requiring `Some` on both sides was tried, is clearly the correct
predicate, and is **load-bearing in its buggy form**: it takes three of
the four example projects red (`input-cursor`, `owned-segmented-buffer`,
`owned-split-buffer`), all with `transport using` premise failures on
`ConditionIs(PointerOffsetEqual(..))` and
`ConditionIs(Bitvector32Equal(..))` facts that differ only by snapshot.
The accidental equivalence is standing in for snapshot-insensitive
matching those examples need. Filed separately; not fixed here because
the premise-policy work does not need it (the four tests and all three
gates are green without it).

### Gates at the end of this work

- `cargo nextest run --lib --bins`: 501 passed, 2 skipped
- `cargo test --test mdtests`: 271/271
- `cargo test --test examples`: pass
- `CLICK_STRICT_EXIT_GATE=1 cargo test --test mdtests`: 2 of 271 failed
  (unchanged from the 2/271 baseline)

Remaining `#[ignore]` in the lib: `expansion_preserves_unfolded_resource_
and_predicate_fact_spellings` (family 2 above, retested and unchanged by
this work) and `verifies_old_memory_loop_invariant` (parked elsewhere).
