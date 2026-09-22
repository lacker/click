# Gaps found while proving a marking search terminates

Tracked by `issues/dfs.md`; delete this directory with that issue.

Current checkpoint: the full search termination and memory-safety proof passes
as `mdtests/search_terminates_by_unmarked_count.md`. Other reductions and
quoted diagnostics below are historical until individually rerun; their
descriptions are not a current test verdict. The deleted
`a_second_universal_have_cannot_narrow_a_stated_range.md` references refer to
the fixed defect listed below, not another missing reproduction.

These files are reductions or historical records, not tests. Current passing
behavior lives in `mdtests/`. The checked examples include
`mdtests/unmarked_count_lemmas.md` (the counting lemmas),
`mdtests/sweep_maintains_a_zero_unmarked_count.md` (the counting invariant
across the store that changes it), and
`mdtests/search_terminates_by_unmarked_count.md` (the complete search proof).

The `decreases unmarked(visited, 0, n)` measure itself is **not** a gap any
more: an `Integer`-valued fold is accepted as a loop measure, and the ranking
bundle it adds is `0 <= unmarked(visited, 0, n)` at the back edge plus a strict
decrease there. Neither is the fold law after a store, which
`sweep_maintains_a_zero_unmarked_count.md` now exercises on master.

- (fixed in 88b05d28: a second universal `have` could not narrow a stated
  `views` range; regression `mdtests/a_second_universal_have_narrows_a_stated_range.md`.)
- `a_universal_fact_does_not_transport.md` — **missing rule.** `transport`
  refuses a quantified proposition (`unsupported proof operation transport`),
  and refuses a comparison too, so a quantified precondition reaches a loop
  body only one cell at a time, through an entry-snapshot `instantiate`, two
  `extract`s, a load-equality transport, and a hand-written orientation flip.
  Nineteen lines for one premise. It is also the escape route from the bug
  above, and it does not reach.
- `return_inside_a_ranked_loop_body.md` — **fixed historical record.** Return
  paths now terminate loop preservation without owing the back-edge bundle;
  `mdtests/return_inside_ranked_loop_body.md` covers explicit and automatic
  preservation.
- `reachability_needs_an_algebraic_loop_witness.md` — **missing proof-language
  representation.** The recursive array walk verifies with `Nat` fuel, but the
  loop cannot carry the changing algebraic witness directly; the numeric,
  `to_nat`, and resource alternatives each hit a specific checked refusal.
- `small_refusals_and_spellings.md` — seven one-to-six-line costs: extent
  halves restated at every `apply`, `arithmetic() using` not weakening a
  derived strict bound, a constant-true requirement needing its own `have`,
  `assumption()` not closing a `viewable` goal, a store refusal spelling the
  owned range against the other parameter's base, `have` not taking a label,
  and theorem proofs not being shareable between mdtests.
