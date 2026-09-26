# Verify a pointer-chasing search over an index array (the "DFS" example)

P1. This issue tracks the DFS forcing-function example. Its acceptance
criteria are met; what remains is proof cost, measured below as the basis for
deciding whether to close it. `design/dfs-gaps/` holds the saved reductions
and design notes and is deleted with this issue. Keep the user's constraints:
the C is fixed, no proof hacks, and a true claim Click cannot prove is a
Click gap.

## Acceptance (met)

- `mdtests/search_terminates_by_unmarked_count.md`: the unchanged
  `next`-chasing loop terminates on `decreases unmarked(visited, 0, n)`, is
  memory safe, and `result == 1` implies an in-bounds, unmarked target reached
  by a finite `walk`.
- `mdtests/branching_graph_dfs.md`: the unchanged cyclic two-successor
  recursive search terminates, is memory safe, a nonzero result gives a finite
  `Path` in the entry graph to an in-bounds target unmarked at entry, and from
  an all-unmarked entry state zero means no finite path reaches the target.
- `mdtests/sweep_maintains_a_zero_unmarked_count.md`: a marking loop keeps
  `unmarked(visited, 0, i) == 0`.
- Shared checked modules: `mdtests/unmarked_count_lemmas.click`
  (`unmarked_nonnegative`, `unmarked_frame`, `unmarked_point_update`) and
  `mdtests/branching_graph_paths.click` (`Path`, `walk`, `walk_frame`,
  `closed_marks_exclude_target`, `exhausted_zero_entry`). The mdtest gate
  verifies each `.click` file as an entry.

## Step 4 of the fold read-range design (landed)

`design/dfs-gaps/fold-read-range-inference.md` step 4 removed the sweep's
prefix-frame scaffolding: one explicit `transport` carries
`unmarked(visited, 0, i) == 0` across `visited[i] = 1` through the kernel's
fold read frame. The same pass removed bookkeeping the other recent
capabilities make obsolete: C-proof `apply` now selects premises (including a
stated range's extent halves) instead of restating them, reflexive transport
sources and constant-true premises need no `have`, loop-head extents need no
`have`, and restatements of call guarantees are gone. The DFS point-update
lemma stays: its store is inside the counted range.

| File | Lines before | Lines after | C-proof work before | after |
| --- | ---: | ---: | ---: | ---: |
| `sweep_maintains_a_zero_unmarked_count.md` | 113 | 88 | 80,122 | 68,499 |
| `sweep_prefix_survives_its_endpoint_store_by_transport.md` | 82 | deleted (now identical to the sweep) | | |
| `search_terminates_by_unmarked_count.md` | 369 | 309 | 69,611 | 53,172 |
| `branching_graph_dfs.md` | 1,147 | 587 | 424,502 | 411,941 |
| `branching_graph_path_witness.md` | 202 | 21, plus 185 in `branching_graph_paths.click` | | |
| `unmarked_count_lemmas.click` | 440 | 273 | 71 ms | 41 ms |

Work is deterministic units summed over the C proof's tactics
(`CLICK_TACTIC_WORK_REPORT`); pure-theorem tactics are not instrumented, so
the lemma library shows wall time. The DFS lost 560 lines mostly by importing
the two modules instead of copying their lemmas. `unmarked_monotone` and
`unmarked_after_first_call_decreases` had no user and were deleted.

## Where the remaining proof text goes

`branching_graph_dfs.md`, 587 lines (about 555 of Click):

| Category | Lines | Kind |
| --- | ---: | --- |
| Failure completeness: compose the two calls' closure summaries, then `exhausted_zero_entry` | ~128 | half inherent; ~70 are instantiations of snapshot equalities for `left`/`right` |
| Framing `visited` across the marking store (target cell, prior marks, prefix/suffix for the point update, `k != cur`) | ~80 | bookkeeping |
| Success paths: open the callee's witness, prepend the edge, frame the path to the entry graph | ~63 | ~40 inherent, rest framing |
| Framing read-only `left`/`right` across the store and the left call | ~60 | bookkeeping |
| Composing call guarantees (target cell unchanged, `cur` still marked, `marked_transitive`, opening `left_result == 0 implies ...`) | ~56 | mixed |
| Ranking arithmetic (point update, nonnegativity, strict decrease, chains through `old`) | ~43 | mostly inherent |
| Early returns (vacuous failure summaries, `Path::Here`) | ~35 | inherent but trivial |
| Resource declaration and `marked_transitive` | ~28 | inherent |
| Contract statement (8 `ensures`) | ~26 | inherent |
| Resource re-observation and successor-bound instantiation for call arguments | ~22 | bookkeeping |

Representative framing text (repeated for `right` and again across the call):

```click
have forall (k: int32) {
    0 <= k and k < n implies old(left[k]) == at(after_mark, left[k])
} by {
    intro(); intro();
    extract(0 <= k); extract(k < n);
    transport(old(left[k]) == old(left[k]), old(left[k]) == at(after_mark, left[k])) using {
        old(left[k]) == old(left[k]);
        0 <= k; k < n;
        separate(memory(left[0..n]), memory(visited[0..n]));
    };
    assumption();
}
```

and, in the completeness proof, six instantiations of the form
`instantiate(forall (k) { ... old(left[k]) == at(before_right, left[k]) }, k)`
followed by `rewrite`s from `old(left[k])` to the snapshot the callee spoke
about.

`search_terminates_by_unmarked_count.md`, 309 lines: `walk` and its two
theorems 96 (`walk_frame` alone 56, used only to frame `next` across the
`visited` store), framing `next` across the store 40, framing `visited` for
the point update 44, witness extension 16 (half framing), contract, loop
header, and ranking 42, setup and statement steps 25.

What a language or tooling change could remove, largest first:

1. **Snapshot stability of a viewed, separated array** (about 60 DFS lines,
   most of the ~70 instantiation lines in completeness, both `walk_frame`
   applications, and in the search `walk_frame` plus ~40 lines). `left`,
   `right`, and `next` are only viewed, and every write in scope is to a
   separated `visited` or through a callee that only views them. The resource
   tracker could answer that the array snapshots are the same resource state,
   so `walk(old(left), ...)` and `walk(at(after_mark, left), ...)` would be
   one term. This is the resource-tracker direction already under design.
2. **A store's frame as one checked fact** (about 80 DFS and 44 search lines).
   After `visited[cur] = 1`, every quantified fact about `visited[k]` with
   `k != cur` needs its own transport, and the point-update lemma wants two
   half-range agreements. A checked store summary
   (`forall k: k != cur implies at(before, visited[k]) == visited[k]`) that
   quantified facts can cite, or `transport` of a whole quantified fact whose
   binder guard excludes the written index without a reflexive source, would
   remove most of it.
3. **Path-condition use of call guarantees** (about 25 DFS lines). Inside the
   branch where `left_result == 0`, opening `left_result == 0 implies X`
   takes an `extract`/`assumption` block each time.
4. **Pure-theorem extent halves** (6 `using` lines per `apply` in the lemma
   library). A pure `apply`, smart or explicit, must still name
   `0 <= n - lo; n - lo <= 1073741823` for a `views` requirement; the C-proof
   route no longer does. This remains the design question of which premises a
   pure checker may read.

The remaining ~250 DFS lines (contract, ranking, witness construction, the
closure-summary case analysis) are the claim's own content. If items 1 and 2
land, the DFS would be roughly 400 lines, dominated by inherent content; that
is a reasonable point to close this issue.

## Findings from the step 4 pass (reported, not filed)

- `click expand` on a C mdtest that imports a local `.click` module failed
  with the imported declarations unknown; fixed on this branch (commit
  "Load an importing C mdtest as a project in click expand") with a
  regression in `src/bin/click-expand.rs`.
- In a pure theorem, smart `apply(walk_in_range(a, n, from, previous));`
  refuses a `views` requirement with "`0 <= n is true` is not an available
  fact" after `have 0 <= n`, `have 0 <= n - 0`, and
  `have n - 0 <= 1073741823` all succeed; the explicit `using` form passes.
  The search selected a candidate its checker rejected.
- The loop's `close_invariants()` closes the quantified `next` bound itself
  when its explicit transport is omitted, but its work rises from about 13k
  to about 250k units; the search keeps the explicit transport.
- Diagnostics: a smart C-proof `apply` missing a `viewable` premise says only
  that the preservation driver declined it; a missing
  `at(iter, viewable(...))` is rendered identically to the available current
  `viewable(...)`; a `simp` refusal about `visited[k]` after a store to
  `visited[cur]` says the store to `next[…]` may have written it.
- `unfold(...) using` still refuses a constant-true premise such as `0 <= 0`
  that `apply using` now accepts; `n <= n` is not constant-folded and still
  needs a `have`.
