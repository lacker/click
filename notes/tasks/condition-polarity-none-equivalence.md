# `condition_polarity_equivalent` treats "no canonical form" as a match

Status: DONE — predicate fixed soundly, all four gates green (including
all four example projects). Two of the three blocked examples were
repaired by regenerating their sidecars; the third needed two more
bridge sites. Ready to land.
Claimed: claude/nervous-ptolemy-90e738 (worktree agent-a156f211eec3701d6), 2026-07-30

Found while fixing the certificate premise policy
(`lib-ignored-expansion-tests.md`, 2026-07-30). Not fixed there: the
premise work does not need it, and fixing it takes three example
projects red.

## The bug

`src/lang/click/proof.rs`, `condition_polarity_equivalent`:

```rust
(Proposition::ConditionIs(lc, lv), Proposition::ConditionIs(rc, rv)) => {
    canonical_order_condition(lc, *lv) == canonical_order_condition(rc, *rv)
}
```

`canonical_order_condition` returns `Option<(Bitvector32Term, Bitvector32Term, bool)>`
and only comparisons have a canonical order form. Everything else — an
overflow check, `PointerOffsetEqual`, `Bitvector32Equal`, a constant —
returns `None`. So **any two conditions that both lack a canonical form
compare equal**.

`condition_polarity_equivalent` backs `exact_fact_contains_conjunct`,
hence `exact_fact_is_available`, which is the availability predicate for
`step using` / `transport using` premises, for statement prerequisites,
and for the certified-transition selection. The predicate therefore
answers "yes, that fact is available" for a non-comparison condition
whenever the available set holds *any other* non-comparison condition.

Observed concretely: in `verifies_loop_invariants_and_statement_assert`
the ambient set holds `ConditionIs(Constant(true), true)`, which made
`ConditionIs(Bitvector32SignedAddOverflows(i, 1), false)` register as
exactly available.

## The fix that landed

`condition_polarity_equivalent` now requires a canonical order form on
both sides:

```rust
matches!(
    (canonical_order_condition(lc, *lv), canonical_order_condition(rc, *rv)),
    (Some(left), Some(right)) if left == right
)
```

Everything else falls to the `left == right` fast path at the top, so two
`None` conditions are equivalent only when they are literally equal.

### The legitimate need, done soundly

Premise matching does genuinely have to accept two spellings of one fact
whose load atoms carry different memory snapshots. That is now an
explicit, proof-backed second chance rather than a side effect:

- `Assumptions::conditions_equal_modulo_proven_snapshots`
  (`src/kernel/assumptions.rs`) walks two conditions with an *exact*
  structural skeleton — only matching constructors recurse, everything
  else falls back to `==` — and compares load atoms with
  `memory_loads_proven_equal`. Structurally different conditions can
  never match, and a load pair is accepted only when the kernel proves
  the two snapshots agree at the loaded pointer.
- `conditions_equal_ignoring_memories` (same file, exported
  `pub(crate)`) is the cheap snapshot-blind version of that same
  skeleton, built on the existing `pointers_equal_ignoring_memories`.
  It is documented as NOT an equivalence: it only narrows the candidate
  set before the proving comparison runs. The two share one skeleton
  (`conditions_equal_with_load_atoms`) so the filter is by construction
  a relaxation of the decision.
- `snapshot_bridged_fact_is_available` (`src/lang/click/proof.rs`) is
  the availability-level wrapper: candidates come only from the
  available facts, assumptions come from the available facts plus an
  optional `framing: &[ExecutionPureFact]` slice of recorded memory
  effects. Exact matching still runs first, and assumptions are built
  only once a candidate exists, so the hot path is untouched.

Sites, each with its soundness argument:

- `exact_fact_is_available` — bridging only ever re-spells a fact that
  is already in `available`, and the re-spelling is accepted only when
  the kernel proves the snapshots agree at every load pointer, so no
  unestablished premise can become available.
- `check_atomic_derivation_goal`'s `premise_part_available` — same, on
  the already-normalised premise part; `framing` is empty there, so only
  assumptions drawn from the listed facts themselves can bridge.
- the `step using` / `apply using` premise check
  (`exact_fact_is_available_across_effects`, with
  `&replay.effect_facts`) — the effect facts contribute no fact of their
  own, only the frame evidence that shows the pre- and post-effect
  snapshots agree at the loaded pointer; a fact still has to be in
  `all_pure_facts` to be found.

### Why not the memory-blind comparison on its own

The obvious cheap fix — equate load atoms by pointer and ignore the
snapshot — is unsound and the repo already forbids it. Kernel test
`memory_load_equality_does_not_ignore_loop_havoc_identity` asserts that
adding a havoc marker makes two loads *not* provably equal, and
`notes/conventions.md` records it as a soundness trap. The failing
examples differ precisely by call-havoc markers, i.e. across calls that
may have written the loaded location, so the memory-blind rule is exactly
the rule that must not decide these.

## The three examples were not blocked, they were wrong (resolved)

With the sound predicate the three projects still fail, and the reason is
not missing machinery. Their `step using` premise lists (which look
machine-generated) contain propositions lowered at the wrong program
point, including flatly false ones:

- `examples/owned-split-buffer/owned_split_buffer.click:398`
  `fact owner->split == (owner->split + 1);` — `x == x + 1`.
  Line 395, `fact ignored == (owner->split + 1);`, is the post-call
  spelling of `ensures result == old(owner->split) + 1`; after
  `owned_split_buffer_move_right` incremented `owner->split` it is false.
- `examples/input-cursor/input_cursor.click:483`
  `fact left->pos == (left->pos + 1);` — same shape.
- `examples/owned-segmented-buffer` fails at
  `owned_segmented_buffer_pipeline.contract` tactic 12 in the same
  family (`transport using` source not derivable).

Evidence that this is a real fact and not a matching gap: at the failing
`owned-split-buffer` premise the loaded pointer is
`arg-memory@(v100000 * 4)` = `owner->split`, and the intervening call's
`CMemoryEffectSummary` declares `mutable_ranges` =
`arg-memory@(v100000 * 4)[0..1]` — exactly that location, correctly
declared, because `move_right` does write `owner->split`. The two
snapshots therefore provably may differ and no sound bridge can equate
them.

So these are the callers the fix was meant to expose: they depended on
junk-equivalence to accept premises that do not hold. The follow-up is to
repair (most likely regenerate) the premise lists in those three
sidecars, not to loosen the predicate.

## How the three examples were resolved

- `input-cursor` and `owned-split-buffer`: the coordinator reverted each
  applied expansion to its pre-expansion proof and re-ran click-expand
  with the current generator. The false unanchored premises are gone —
  e.g. `fact left->pos == (left->pos + 1);` became
  `fact left->pos == (at(statement(5).entry, left->pos) + 1);`. Both
  verify green with the sound predicate. This confirms the diagnosis:
  the premises were wrong, and the generator now spells them at the
  point where the fact actually holds.
- `owned-segmented-buffer`: not a regenerated region. An original
  hand-written `transport using` at
  `owned_segmented_buffer_pipeline.contract` tactic 12 needed two more
  bridge sites in `replay_linear_tactics`. The sidecar itself is
  correct and was not touched.

### The two extra sites

The failing tactic is
`transport(at(statement(4).entry, owner->first_len) == at(statement(4).entry, first_len), owner->first_len == first_len)`.
Its source and its listed fact both spell `at(statement(4).entry, ...)`
but lower to snapshots differing by one call-havoc marker (and an
irrelevant `local:ignored` cell), because one side comes from a recorded
lowering and the other from a fresh one.

- Source availability: `exact_fact_is_available(&source, &explicit_premises)`
  now falls back to `snapshot_bridged_fact_is_available_under`, which
  takes the caller's `selected_assumptions` plus `replay.effect_facts`.
  Sound because candidates still come only from `explicit_premises` —
  the transport must still list the fact — and the wider assumption
  context only decides whether two spellings denote one fact.
- Target availability: `exact_fact_is_available(&target, &requirement_pure_facts)`
  became `exact_fact_is_available_across_effects` with the same framing.
  The bug was masking this one too: `owner->first_len == first_len` is a
  `Bitvector32Equal`, so with `None == None` the target counted as
  already available and the tactic `continue`d, skipping the certified
  frame transport entirely. Sound because candidates come from the same
  ambient fact set the exact check already used.

Note the coordinator's first attempt put the bridge in
`replay_fact_transport_at_outcome` (the `path {n}, tactic {n}` site).
That is a legitimate site and was kept, but it is not the one that
fires here — the failing message has no `path` prefix, which is how the
three `requires a source derivable` sites are told apart.

## Gates

All four green:

- `cargo nextest run --lib --bins` — 509/509, 3.1 s.
- `cargo test --test mdtests` — green, 8.8 s.
- `cargo test --test examples` — ALL FOUR projects green:
  input-cursor 1.42 s, jsonc-refcount 0.07 s,
  owned-segmented-buffer 5.19 s, owned-split-buffer 2.89 s.
  Against the pre-fix baseline (1.27 / 0.08 / 6.14 / 3.64 s) there is no
  slowdown — the bridge stays off the hot path.
- exit gate unconditional.

Regression tests:

- `lang::click::tests::unrelated_non_comparison_conditions_are_not_polarity_equivalent`
  pins the bug closed (overflow / constant / equality pairwise
  non-equivalent, self-equivalence and the comparison canonical form
  still work).
- `kernel::tests::conditions_equal_modulo_proven_snapshots_needs_frame_evidence`
  pins the substitute match: same snapshot matches, an unframed call
  havoc does not, an effect summary framing the loaded pointer restores
  the match, and structure is never relaxed.
- The three example projects themselves pin the site wiring.

## Dead ends

- Bridging with `available` alone: fixes the `derive` premise site in
  `owned-split-buffer` (`have proof 20`) but not the `step using` sites,
  which need the recorded effect facts as frame evidence. Hence the
  `framing` parameter.
- Adding the effect facts still does not close it: the frame evidence
  exists and is correctly shaped (`memory_snapshots_directly_proven_equal_for_load`
  does handle `CMemoryEffectSummary`), but the declared mutable range
  covers the loaded pointer. Confirmed with a temporary probe in that
  function; the endpoints matched and `ranges_proven_disjoint_from_pointer`
  was false.
- Full derivation (`derive_simp_proposition`) instead of exact matching
  would make the examples pass but weakens "exact premise" into
  "derivable premise", which is a separate, weaker check the code
  already distinguishes. Not done.
- Auto-transporting premises inside availability would also close it,
  but silently transporting is a Surface Click semantics change and
  needs the owner's call. Not needed in the end: bridging the two
  availability checks was enough, and it keeps transport explicit.
- Bridging only the source check in `replay_linear_tactics` moves the
  failure to `no certified frame transport applies` — that is the
  target check short-circuit the bug was also hiding, not a real
  transport gap.

Repro for the example failures: `cargo test --test examples`, or one at a
time with `CLICK_EXAMPLE_CHILD_PATH=$PWD/examples/<name> cargo test
--test examples -- --nocapture` (the isolated child's stderr is not
forwarded by the parent harness, so use the child path when probing).
