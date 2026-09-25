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
`branching_graph_dfs.md` records the unchanged branching C search, now checked
for termination, memory safety, success reachability, and failure completeness
from all-unmarked entry in `mdtests/branching_graph_dfs.md`. `mdtests/unmarked_count_lemmas.md` now also checks the
count-monotonicity lemma required between its two recursive calls.

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
- `reachability_needs_an_algebraic_loop_witness.md` — **fixed historical
  reduction.** Algebraic `forall`, `exists`, `witness`, and `choose` now carry
  changing `Nat` witnesses, including from an explicit loop invariant. The
  full `search` proof transports `walk` across the visited-array store in
  `mdtests/search_terminates_by_unmarked_count.md`.
- `branching_graph_dfs.md` — the two-successor cyclic-graph reduction and its
  next proof obligations; unlike the verified binary-tree DFS, its left call
  can change `visited` before the right call.
- `small_refusals_and_spellings.md` — seven one-to-six-line costs: extent
  halves restated at every `apply`, `arithmetic() using` not weakening a
  derived strict bound, a constant-true requirement needing its own `have`,
  `assumption()` not closing a `viewable` goal, a store refusal spelling the
  owned range against the other parameter's base, `have` not taking a label,
  and theorem proofs not being shareable between mdtests.

- `fold-read-range-inference.md` — requested design proposal, not implemented.
  No new syntax is proposed; checked application-specific fold support would
  simplify the sweep's prefix framing. The document separates explicit
  framing from automatic range naming and specifies soundness and scaling gates.
