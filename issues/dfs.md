# Verify a pointer-chasing search over an index array (the "DFS" example)

P1. This issue tracks the DFS forcing-function example and the language gaps it
found. Kernel soundness review discovered during the same campaign is tracked
separately in `issues/bughunt.md`. Everything needed for this example is here
and in `design/dfs-gaps/`; nothing depends on anyone's scratch files.

## Handoff checkpoint — 2026-09-22, after the reachability attempt

The complete unmodified search now verifies termination and memory safety in
`mdtests/search_terminates_by_unmarked_count.md`. Its `Integer`-valued fold
measure, quantified `next` invariant, early return, checked store, point-update
lemma, nonnegativity proof, and strict back-edge decrease all pass together in
the gate. The same proof now establishes that `result == 1` implies `to` is in
bounds and `visited[to] == 0`: success can only use the `cur == to` return,
which precedes the marking store. `unmarked_nonnegative` also lives with the
other checked counting lemmas in `mdtests/unmarked_count_lemmas.md`.

Graph reachability now has first-class algebraic quantifiers and ghost
witnesses. `mdtests/algebraic_existential_witness.md` checks algebraic
`exists`, `forall`, `witness`, and `choose`, including reuse beneath
`Nat::Succ`; `mdtests/algebraic_existential_loop_witness.md` opens an explicit
`invariant N` source and rebuilds a changing `Nat` witness at the back edge.
No C bookkeeping or produced token is involved.

Applying the same mechanism to `walk(next, from, fuel)` exposed the next
independent boundary: after the store to the disjoint `visited` array, the
chosen relation names `next` at the iteration-entry memory snapshot while the
successor defining equation names it at the current snapshot. Click does not
yet transport that recursive pure-function equality across the disjoint
store. The updated reduction is in
`design/dfs-gaps/reachability_needs_an_algebraic_loop_witness.md`. The
algebraic witness representation is no longer the blocker; snapshot-stable
transport of the array-dependent relation is.

The focused `mdtests/recursive_walk_survives_unrelated_store.md` now proves a
sound alternative to opaque-function transport: an inductive `walk_frame`
lemma derives equality from pointwise equality over the viewed `next[0..n]`
range. Its store regression uses an explicit separation requirement between
`next` and `visited`; mere distinct parameter names are not sufficient.
Nested `instantiate` and theorem application now accept algebraic bindings
chosen in proofs (`mdtests/algebraic_induction_binding_in_have.md` and the
extended `mdtests/algebraic_existential_loop_witness.md`). In the complete
search attempt, initialization and back-edge construction of the existential
witness passed, but `close_invariants()` could not re-establish that fact at
its own back-edge snapshot. Keep the complete proof attempt out of the green
fixture until that closure transport is reduced and repaired.

The explicit
quantified-transport, whole-array dependency, shared-lemma, extent-restatement,
and small diagnostic items below remain proof-language or tooling costs, but
none blocks the termination, memory-safety, or branch-local correctness claims.

Whole-array dependency refinement, reachability, and recursive DFS remain
design work rather than small finishing edits. In particular, discuss the
fold-read-range design in item 2 with the user before implementing it.

This file is the index; `design/dfs-gaps/` contains the saved C/Click sources.
Those files include historical diagnostics, and other small gaps/tooling notes
below have not all been retested on this commit. In particular, the old
`a_second_universal_have_cannot_narrow_a_stated_range.md` defect was fixed in
`88b05d28`; its checked regression is
`mdtests/a_second_universal_have_narrows_a_stated_range.md`. Do not reopen it
merely because an old reduction mentions its former filename.

Preserve the user's design constraints: keep the C fixed, avoid proof hacks,
and discuss a proof-language migration when it offers a simpler design.
Direct aggregate `views` remain restricted; use declared resources and the
accepted pointer/array forms documented in `docs/concepts/resources.md` and
`docs/concepts/viewability.md`. The fold-read-range design in item 2
still needs discussion before implementation. No scratch files or conversation
history are required to reproduce the current blocker.

---

# The DFS example

An `int next[n]` array whose entries are all in `0..n` (indexes used as
pointers), a `visited[n]` array, and a search that follows `next`, marks
`visited`, and reports whether `to` is reached. Prove it terminates (termination
is the only C judgment), is memory safe, and then a correctness claim. The C is
fixed; a true claim Click cannot prove is a Click gap.

```c
int32 search(int32 *next, int32 *visited, int32 n, int32 from, int32 to) {
    int32 cur = from;
    while (visited[cur] == 0) {
        if (cur == to) return 1;
        visited[cur] = 1;
        cur = next[cur];
    }
    return 0;
}
```

The measure is a user-defined `Integer`-valued fold (not the prelude `count`,
which clashes with the built-in `count(resource(args))`; not `int32`, whose `+`
is partial in specs), used as `decreases unmarked(visited, 0, n)`:

```click
function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}
```

## State

- On master and verifying: `mdtests/unmarked_count_lemmas.md` (`unmarked_frame`,
  `unmarked_point_update`, by `induct(hi)`) and
  `mdtests/sweep_maintains_a_zero_unmarked_count.md` (a marking loop keeping
  `invariant unmarked(visited, 0, i) == 0`; it carries a verbatim copy of
  `unmarked_frame`).
- `mdtests/search_terminates_by_unmarked_count.md` checks the complete C and
  sidecar for `search`, including the success-path result claim. The formerly
  saved blocked proof now verifies without changing the C.

## Gaps, ranked by the proof text they cost (reductions in `design/dfs-gaps/`)

1. **A quantified fact cannot be explicitly transported to another program point**
   (`a_universal_fact_does_not_transport.md`). `transport` refuses a quantified
   proposition and a comparison (`unsupported proof operation transport`), so a
   quantified precondition reaches a loop body one cell at a time — 19 lines per
   premise. A top-level `transport` in a `preserve` body verifies while the same
   `transport` inside a `have` there is refused. The automatic invariant route
   used by `search` now passes, but the explicit language gap remains.
2. **A fact about part of an array dies at a store outside that part.**
   `unmarked(visited, 0, i)` reads only cells below `i`, but Click records that it
   depends on the whole array, so `visited[i] = 1` discards it; the user pays with
   a frame lemma plus a quantified per-cell transport (about 110 of the sweep
   example's 190 lines). Design idea, **not approved by the user — ask first**:
   derive the read range from a fold-shaped definition (`(lo..hi).fold` whose body
   reads `v[k]` at exactly the binder; anything else falls back to the whole
   array, default-deny because a too-small range is a false theorem), carry it on
   the array argument, and let the resource tracker's assumption-free walk decide
   that a store to `a[i]` misses `a[0..i)` because the stored index is the same
   term as the upper bound. It would not help `search` itself (that store is
   inside the range; `unmarked_point_update` is genuinely needed).
3. **No gate-checked shared lemma library for mdtests.** `import` supplies
   theorem statements and assumes their proofs by design, and nothing in
   `scripts/check.sh` selects a library `.click` file, so lemmas are copied
   verbatim into each example.
4. **Extent bounds restated at every pure-theorem `apply … using`.** A stated
   range carries `0 <= n - lo` and `n - lo <= 1073741823` for the proof, but a
   `using` list in a pure theorem must name them again (the C-proof route accepts
   a cited range's available guards). That checker promises to read only listed
   premises, so this is a design question.
5. Small ones (`small_refusals_and_spellings.md`): no `!=` symmetry (forces
   `unmarked_point_update`'s `below`/`above` split; not re-tested recently);
   `have` cannot take a label; `assumption()` cannot close a `viewable` goal;
   `arithmetic() using { j < hi; hi <= n }` will not weaken to `j <= n` and says
   the premises are insufficient; `missing pure fact: constant condition is true`
   does not say which constant; a store refusal spells `owns b[0..1]` as
   `owns a[(v100001 - v100000)..]`.

Next stages: make the recursive `walk` relation stable across the disjoint
`visited` store, use the now-supported algebraic witness to prove reachability
for this search, then move to the recursive branching DFS. The older
folded-resource route has its own gaps:
a loop guard cannot read a cell owned by a folded resource, and recursive
`walk` is not allowed in a resource fact.

## Acceptance

Termination and memory safety of the unmodified C are checked by
`mdtests/search_terminates_by_unmarked_count.md`, along with the branch-local
success claim. For the remaining work, each fixed gap has a minimal regression
mdtest, reachability is proved or split out at the user's request, and
`design/dfs-gaps/` is deleted with this issue.
