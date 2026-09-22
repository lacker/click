# Gaps found while proving a marking search terminates

Tracked by `issues/dfs.md`; delete this directory with that issue.

Current checkpoint: the full saved search was rerun unchanged at `624146d4`
on 2026-09-21 and still fails its quantified viewability obligation at the
loop back edge. Other reductions and quoted diagnostics below are historical
until individually rerun; their descriptions are not a current test verdict.
The deleted `a_second_universal_have_cannot_narrow_a_stated_range.md` references
refer to the fixed defect listed below, not another missing reproduction.

These files are reductions, not tests. They do not verify, so they are not in
`mdtests/`. Each one is the smallest thing that still fails, with the exact
refusal it produces and the rule that would make it pass. The two examples that
do verify are `mdtests/unmarked_count_lemmas.md` (the counting lemmas) and
`mdtests/sweep_maintains_a_zero_unmarked_count.md` (the counting invariant
across the store that changes it).

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
- `return_inside_a_ranked_loop_body.md` — **missing rule** plus a **bad
  diagnostic.** A `return` is not one of the loop rule's three body endings, so
  the documented proof-level-`if` route refuses it honestly and the `loop`
  automation refuses it with the wrong tactic index. `branch { then {
  execute(); } else { } }` does accept a returning arm, but only when an
  unrelated fact is in the context first, and its refusal otherwise
  (`branch did not verify as a checked preservation operation`) names nothing
  at all.
- `small_refusals_and_spellings.md` — seven one-to-six-line costs: extent
  halves restated at every `apply`, `arithmetic() using` not weakening a
  derived strict bound, a constant-true requirement needing its own `have`,
  `assumption()` not closing a `viewable` goal, a store refusal spelling the
  owned range against the other parameter's base, `have` not taking a label,
  and theorem proofs not being shareable between mdtests.
- `search_terminates_blocked.md` — the stage-3 example itself, at the furthest
  point it reaches. Everything verifies except the last bundle member: the
  contract, the memory safety of the walk, the `Integer` measure's
  well-formedness, the quantified `next` bound instantiated at `cur`, the early
  `return` arm, the point update between `at(iter, visited)` and `visited`, the
  nonnegativity of the count, and the strict decrease. What stays open is the
  *viewability* half of the quantified invariant at the back edge, for the
  reason in `a_universal_fact_does_not_transport.md` (the binder bug that used to be
  listed first here is fixed).
