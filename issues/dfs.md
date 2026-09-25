# Verify a pointer-chasing search over an index array (the "DFS" example)

P1. This issue tracks the DFS forcing-function example and the language gaps it
found. Kernel soundness findings discovered during the same campaign are
tracked in `bugs/`. Everything needed for this example is here and in
`design/dfs-gaps/`; nothing depends on anyone's scratch files.

## Handoff checkpoint — 2026-09-25, after branching failure completeness

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

The whole-array dependency, extent-restatement, and small diagnostic items
below remain proof-language or tooling costs, but
none blocks the termination, memory-safety, or branch-local correctness claims.
The shared-lemma gate gap is closed: the mdtest harness now verifies local
`.click` modules as entries, and the unmarked lemmas have one checked source.
The explicit quantified-transport gap is closed too: checked fixtures now
carry the original bounded-value quantifier and a comparison through a
separated store inside `have`, and reject a changed cell.

Whole-array dependency refinement remains design work rather than a small
finishing edit. The unchanged cyclic, two-successor C search now verifies
termination and memory safety in `mdtests/branching_graph_dfs.md`. Its recursive
contract establishes that `unmarked` cannot increase; the local marking store
decreases it by one, so the second call still descends after the first call may
mark more nodes. The successor bounds live in a viewed resource and are
re-observed after the mutating call. Success-path reachability for this graph
search now verifies too, with a finite `Path` witness in the entry graph and
an in-bounds target that was unmarked at entry. The recursive contract also
preserves each previously marked node. Failure completeness from all-unmarked
entry is also checked, using the closed-successor summary described below.
Both recursive success branches and their snapshot framing are checked; see
`design/dfs-gaps/branching_graph_dfs.md`. The proposed fold-read-range design is recorded in
`design/dfs-gaps/fold-read-range-inference.md`; implementation is still pending.

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
`docs/concepts/viewability.md`. The fold-read-range design in item 2 now has a written proposal; its
application-range representation still needs implementation review. No scratch files or conversation
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

- On master and verifying: `mdtests/unmarked_count_lemmas.click`
  (`unmarked_frame`, `unmarked_point_update`, by `induct(hi)`) and
  `mdtests/sweep_maintains_a_zero_unmarked_count.md` (a marking loop keeping
  `invariant unmarked(visited, 0, i) == 0`; it imports the checked lemma).
- `mdtests/search_terminates_by_unmarked_count.md` checks the complete C and
  sidecar for `search`, including the success-path result claim. The formerly
  saved blocked proof now verifies without changing the C.

## Gaps, ranked by the proof text they cost (reductions in `design/dfs-gaps/`)

1. **Resolved: explicit transport of quantified and comparison facts.** The
   historical reduction is `a_universal_fact_does_not_transport.md`.
   `mdtests/quantified_fact_explicit_transport_inside_have.md` carries both a
   bounded-value precondition and a quantified snapshot equality through a
   separated store inside `have`.
   `mdtests/loop_symbolic_disjoint_array_store_frame.md` uses one quantified
   transport inside a loop `preserve` proof in place of per-cell transport.
   `mdtests/comparison_fact_explicit_transport_inside_have.md` checks the
   comparison form, and
   `mdtests/quantified_fact_explicit_transport_rejects_changed_cell.md` checks
   that a write to the read cell is refused.
2. **A fact about part of an array dies at a store outside that part.**
   `unmarked(visited, 0, i)` reads only cells below `i`, but Click records that it
   depends on the whole array, so `visited[i] = 1` discards it; the user pays with
   a frame lemma plus a quantified per-cell transport (about 110 of the sweep
   example's 190 lines). Design proposal (implementation pending):
   The requested design is now in `design/dfs-gaps/fold-read-range-inference.md`.
   It proposes no new syntax: derive a kernel-checked summary for a narrow
   fold subset, attach support to the application rather than the array, and
   establish explicit framing before automatic reuse. It records byte-range,
   aliasing, snapshot, and scaling requirements. Implementation is not yet
   authorized. This would simplify the sweep prefix proof; it would not
   remove the DFS point-update lemma for an in-range write.
3. **Resolved: gate-checked shared lemma library for mdtests.** `import` still
   supplies theorem statements without checking imported proof bodies. The
   mdtest harness now selects every local `.click` file as its own entry, so
   `mdtests/unmarked_count_lemmas.click` checks the proof bodies while the
   search and sweep import their statements. The three copies of
   `unmarked_frame` and the search's other copied unmarked lemmas are removed.
4. **Extent bounds restated at every pure-theorem `apply … using`.** A stated
   range carries `0 <= n - lo` and `n - lo <= 1073741823` for the proof, but a
   `using` list in a pure theorem must name them again (the C-proof route accepts
   a cited range's available guards). That checker promises to read only listed
   premises, so this is a design question.
5. Small ones (`small_refusals_and_spellings.md`): int32 `!=` symmetry is now
   checked by `mdtests/int32_disequality_symmetry.md`. The point-update
   theorem still splits below/above to cover both sides of the marked index.
   `have` cannot take a label; `assumption()` cannot close a `viewable` goal;
   `arithmetic() using { j < hi; hi <= n; }` now proves `j <= n` in one checked
   step; a constant-true `using` premise such as `0 <= 0` is accepted
   (`mdtests/apply_using_accepts_a_constant_true_premise.md`) and a false one
   names itself; a store refusal spells `owns b[0..1]` as
   `owns a[(v100001 - v100000)..]`.

The unchanged two-successor graph search now checks termination, memory
safety, and success-path reachability in `mdtests/branching_graph_dfs.md`,
including the right recursive call after the left has changed `visited`.
Failure-path completeness now checks too: from an all-unmarked entry state,
returning zero implies that every finite `Path` misses the target. The recursive
contract still permits arbitrary initial marks. It preserves the target cell,
marks the failed call's root, and makes every newly marked node's successors
marked. This summary composes across both calls; path induction gives the
public theorem. Arbitrary initial marks cannot support ordinary completeness,
since a previsited node can block exploration of a reachable target. A binary-tree recursive search is also
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

The follow-up reachability proof now verifies in `mdtests/branching_graph_dfs.md`.
`walk_frame` in `mdtests/branching_graph_path_witness.md` proves that bounded
successor arrays equal on `0..n` give equal endpoints for every finite path.
The DFS proof opens each recursive call's historical witness, prepends its
edge, and frames the longer path back to the entry graph. Its per-node
marking summary recovers the target's entry-state zero from the recursive
call's entry-state zero.

Two focused regressions protect the verifier fixes needed by this composition:
`mdtests/graph_view_survives_marked_summary_call.md` checks symbolic-index
framing across a separated call, and
`mdtests/conditional_algebraic_witness_contract.md` checks final certification
of a proved conditional algebraic existential. Kernel regressions reject
missing index/extent bounds, changed graph snapshots, captured free witnesses,
and different witness sorts, and pin indexed lookup scaling. The fold-range
design in item 2 now has a written proposal and has not been implemented.

The completeness contract additionally checks reported algebraic universal
introductions and typed alpha matching of quantified conditional facts in
`mdtests/conditional_algebraic_universal_contract.md`. Kernel regressions
protect guards, graph snapshots, endpoint values, binder sorts, and indexed
lookup scaling. Its expansion regression also checks quantified `have` source
mapping and explicit assumption checking with renamed quantified guards.
No fold-range inference was added.

## Acceptance

Termination, memory safety, and success-path reachability of the unmodified C
are checked by `mdtests/search_terminates_by_unmarked_count.md` and
`mdtests/branching_graph_dfs.md`. The branching DFS also checks failure-path
completeness from an all-unmarked entry state. Remaining work concerns the
proof-language and tooling costs ranked above; each fixed gap has a minimal regression mdtest, and
`design/dfs-gaps/` is deleted with this issue.
