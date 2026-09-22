# Verify a pointer-chasing search over an index array (the "DFS" example)

P1. This issue tracks the DFS forcing-function example and the language gaps it
found. Kernel soundness review discovered during the same campaign is tracked
separately in `issues/bughunt.md`. Everything needed for this example is here
and in `design/dfs-gaps/`; nothing depends on anyone's scratch files.

## Handoff checkpoint — 2026-09-22, after correcting the store frontier

Both the value and generated viewability halves of the quantified invariant
over `next` now close. The direct pointer-chasing route is covered by
`mdtests/loop_quantified_value_after_pointer_chase.md`. A return inside a
ranked loop body also works through the documented proof-level `if` and the
automatic preservation planner; `mdtests/return_inside_ranked_loop_body.md`
covers both routes.

The supposed post-store failure was not a verifier defect. The false arm of
the lowered C `if` contains an explicit `Skip`: the saved proof stepped into
that arm and across the `Skip`, then stated `visited[cur] != 0` before it had
executed `visited[cur] = 1`. The saved proof now has the missing store step.
`mdtests/post_store_fact_after_ranked_loop_return.md` checks the exact control
shape and proves both `b[i] == 1` and `b[i] != 0` immediately after the store.

This is **not yet a routine cleanup handoff**:

- The saved full proof has not yet been promoted into the mdtest gate. Its next
  bounded task is to rerun the corrected source and record the first genuine
  open obligation; do not reopen the now-passing quantified invariant, return,
  or post-store paths.
- Moving an already verified lemma into the checked lemma fixture, refreshing
  old reproductions, and reducing a diagnostic are bounded tasks suitable for
  a less capable agent. Whole-array dependency refinement, reachability, and
  recursive DFS remain design work, not small finishing edits.

For a bounded next assignment, rerun the corrected complete source in
`design/dfs-gaps/search_terminates_blocked.md` and reduce only its new first
failure. The previously quoted `visited[cur] != 0` refusal was before the
store and is no longer evidence of a Click gap.

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
- `design/dfs-gaps/search_terminates_blocked.md` is the full C and sidecar for
  `search` at the furthest point reached. Its false-arm cursor now explicitly
  crosses the lowered `Skip` and the store before using the store result. The
  quantified `next` obligations, return path, and post-store value are all
  regression-covered. Rerun the corrected saved proof to find its next genuine
  refusal.
  It also holds a third lemma, `unmarked_nonnegative`, that verifies and should
  move into `mdtests/unmarked_count_lemmas.md`.

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

Later stages: a modest correctness claim (`result == 1` only via the `cur == to`
exit), then reachability (needs recursive pure functions over arrays — they use
`fuel: Nat` today — or a resource whose field is a pure model of the graph; the
model route has its own gaps: a loop guard cannot read a cell owned by a folded
resource, and there is no spelling for a model field at the head of an
iteration), then the recursive branching DFS.

## Acceptance

`mdtests/search_terminates_by_unmarked_count.md` verifies termination and memory
safety of the unmodified C; each fixed gap has a minimal regression mdtest; a
correctness claim is proved or split out at the user's request;
`design/dfs-gaps/` is deleted with this issue.
