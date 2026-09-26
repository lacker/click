# framing and point-updating a counting measure

`unmarked(v, lo, hi)` counts the cells of `v[lo..hi]` that hold zero. It is the
measure a pointer-chasing search that marks cells as it visits them descends
on, so such a proof needs that the count is nonnegative
(`unmarked_nonnegative`) and drops by exactly one when a previously unmarked
cell inside the range is marked (`unmarked_point_update`). Its boundary case
uses `unmarked_frame`: two arrays that agree below the marked cell count the
same prefix. All three are ordinary `induct(hi)` proofs over the
append-last-cell law `unfold(unmarked(..)) using { lo <= hi - 1; hi - 1 <
2147483647; }` opens. A C proof does not need `unmarked_frame` for a store
outside the counted range: the kernel's fold read frame carries the
application across it (`sweep_maintains_a_zero_unmarked_count.md`).
Their proof bodies live in `unmarked_count_lemmas.click`, which the mdtest gate
checks as an entry module. This fixture imports the same declarations used by
the search, sweep, and branching DFS proofs.

Two things about the statements are forced rather than chosen.

The counted range ends at `hi`, the endpoint the induction descends on, but the
quantified premise that relates `a` and `b` is stated over a separate bound with
`hi <= m`. A premise that mentioned `hi` could not be supplied at `hi - 1`: the
induction hypothesis owes the premise the *kernel* gets by substituting
`hi := hi - 1`, and no surface spelling produces it, because writing `hi - 1`
inside a quantifier body lowers a definedness guard for the subtraction *into*
the body, in front of the written implication. `m` never moves, so the premise
at the smaller endpoint is the same proposition.

`unmarked_point_update` says "`b` is `a` with cell `j` marked" with two
half-range agreements, below `j` and above `j`, rather than one range with
`k != j`. The `k != j` spelling is provable at only one of the two places that
need it: `k < j` gives `k != j` through `int32_lt_implies_neq`, but the
symmetric `hi - 1 != j` from `j < hi - 1` needs a disequality symmetry Click
does not have. Split at `j`, each instantiation gets the orientation it can
prove, and the boundary case hands `unmarked_frame` its premise verbatim.

The ranges are `views` clauses. A stated range carries its extent half beside
its viewability half, so the proof never derives `0 <= n - lo` — but every
`apply` still owes both halves by name, which is the six `using` lines that
restate what the clause above them already said.

```click
import "unmarked_count_lemmas.click";
```

```expect
pass
```
