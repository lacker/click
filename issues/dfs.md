# Verify a pointer-chasing search over an index array (the "DFS" example)

P1. This issue tracks the DFS forcing-function example and the language gaps it
found. Kernel soundness findings discovered during the same campaign are
tracked in `bugs/`. Everything needed for this example is here and in
`design/dfs-gaps/`; nothing depends on anyone's scratch files.

## Handoff checkpoint — 2026-09-22, after branching termination proof

The complete unmodified search now verifies termination and memory safety in
`mdtests/search_terminates_by_unmarked_count.md`. Its `Integer`-valued fold
measure, quantified `next` invariant, early return, checked store, point-update
lemma, nonnegativity proof, and strict back-edge decrease all pass together in
the gate. The same proof establishes that `result == 1` implies `to` is in
bounds, `visited[to] == 0`, and some finite `walk(next, from, fuel)` reaches
`to`: success can only use the `cur == to` return, which precedes the marking
store. `unmarked_nonnegative` also lives with the other checked counting lemmas
in `mdtests/unmarked_count_lemmas.md`.

Graph reachability now has first-class algebraic quantifiers and ghost
witnesses. `mdtests/algebraic_existential_witness.md` checks algebraic
`exists`, `forall`, `witness`, and `choose`, including reuse beneath
`Nat::Succ`; `mdtests/algebraic_existential_loop_witness.md` opens an explicit
`invariant N` source and rebuilds a changing `Nat` witness at the back edge.
No C bookkeeping or produced token is involved.

The complete search now carries an existential `walk` witness through the
loop. It uses the inductive `walk_frame` lemma from
`mdtests/recursive_walk_survives_unrelated_store.md` to relate iteration-entry
and post-store `next` snapshots, then constructs `Nat::Succ(previous)` at the
back edge. `mdtests/algebraic_existential_backedge_snapshot.md` covers the
previous `close_invariants()` failure: alpha-equivalent quantified facts now
match through a typed, snapshot-aware key for array-dependent function
applications, while changed array snapshots do not. Symbolic frame transport
also needs explicit bounds for both its read index and the store's write
index; `mdtests/loop_symbolic_disjoint_array_store_frame.md` checks that path.
The earlier reduction in
`design/dfs-gaps/reachability_needs_an_algebraic_loop_witness.md` is historical.

The explicit
quantified-transport, whole-array dependency, shared-lemma, extent-restatement,
and small diagnostic items below remain proof-language or tooling costs, but
none blocks the termination, memory-safety, or branch-local correctness claims.

Whole-array dependency refinement remains design work rather than a small
finishing edit. The unchanged cyclic, two-successor C search now verifies
termination and memory safety in `mdtests/branching_graph_dfs.md`. Its recursive
contract establishes that `unmarked` cannot increase; the local marking store
decreases it by one, so the second call still descends after the first call may
mark more nodes. The successor bounds live in a viewed resource and are
re-observed after the mutating call. Success-path reachability for this graph
search remains the next proof claim; see
`design/dfs-gaps/branching_graph_dfs.md`. In particular, discuss the
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

Next stage: prove success-path reachability for the unchanged two-successor
graph search in `design/dfs-gaps/branching_graph_dfs.md`, with a finite
left/right path in the entry graph. Termination and memory safety, including
the second recursive call after the first has changed `visited`, are checked
by `mdtests/branching_graph_dfs.md`. A binary-tree recursive search is also
verified in `examples/modeled-binary-tree/`, but that resource-ranked acyclic
case does not cover cycles or sharing. The older folded-resource loop-guard
claim is not a general current limitation;
`mdtests/composite_resource_vector_fill_loop_snapshot.md` already checks a
guard reading a folded owned composite. Re-reduce any particular recursive
resource refusal before treating it as a verifier defect.

## Historical-read lowering resolved (2026-09-25)

Logical memory reads are now total terms. Lowering an ordinary proposition
no longer inserts read-validity or viewability guards. A call-produced
existential using an evaluated C argument therefore has the same denotation
as its historical surface spelling, including beneath a written implication.

`mdtests/call_existential_evaluated_load_guard.md` is a positive regression:
it cites the call guarantee with `at(before_call, a[i])` and opens its path
witness with `let satisfy`. The conditional variant in
`mdtests/conditional_call_existential_historical_read.md` establishes the
nonzero branch, cites the implication, and opens its consequent. Neither
changes the callee contract to carry proof-only validity guards.

Validity is explicit: `defined(p[k])` names typed read validity at the selected
snapshot. `mdtests/explicit_read_validity_uses_the_selected_witness.md` rejects
using validity at a different witness. Logical value facts cannot grant C
read permission or initialize heap memory, and validity does not survive a
free. Resource footprint evaluation and actual C loads remain checked.
Partial C arithmetic still has its existing definedness obligations.

The full DFS reachability proof remains follow-up work. The saved design
records the historical left-success failure, but that citation mismatch is
now covered by positive regressions. Resume the unchanged C from the
left-success branch; proving the longer path and transporting its graph
snapshot are separate proof steps. The fold-range design in item 2 above is
still unapproved and is outside this refactor.

## Acceptance

Termination, memory safety, and success-path reachability of the unmodified C
are checked by `mdtests/search_terminates_by_unmarked_count.md`. For the
remaining work, each fixed gap has a minimal regression mdtest, and
`design/dfs-gaps/` is deleted with this issue.
