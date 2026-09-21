# Verify a pointer-chasing search over an index array (the "DFS" example)

P1. A forcing-function example: an `int next[n]` array whose entries are all in
`0..n` (indexes used as pointers), a `visited[n]` array, and a search that
follows `next`, marks `visited`, and reports whether `to` is reached. The goal
is to prove it **terminates** (termination is the only C judgment in Click) and
is memory safe, then to prove a correctness claim, and to use everything that is
awkward along the way to improve the language rather than the example. The C is
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

The measure is the number of unmarked cells, a user-defined `Integer`-valued
fold in the sidecar (not the prelude `count`, which clashes with the built-in
`count(resource(args))`, and not `int32`, whose `+` is partial in specs):

```click
function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}
```

with loop clause `decreases unmarked(visited, 0, n)`.

## What is on master

- `mdtests/unmarked_count_lemmas.md` — `unmarked_frame` (two arrays agreeing on
  `lo..m` have equal counts on `lo..hi`, `hi <= m`) and `unmarked_point_update`
  (marking one unmarked cell `j` in range drops the count by exactly one), both
  by `induct(hi)`, using `views` clauses in theorems, `unfold(f(args)) using
  { guards }` and Integer `arithmetic() using`.
- `mdtests/sweep_maintains_a_zero_unmarked_count.md` — a `for` loop that marks
  every cell while maintaining `invariant unmarked(visited, 0, i) == 0`. It
  carries a verbatim copy of `unmarked_frame` (see "shared lemmas" below) and a
  quantified per-cell frame fact.
- Language work the example has already forced, all landed: `decreases` over a
  pure (and `Integer`-valued) expression at loops, self-recursion and recursion
  inside loops; loops inside branch arms; theorem application to arrays at a
  snapshot (`at(label, a)`); fold endpoint laws and `unfold … using`; `views`
  in pure theorems; `loadable` renamed `viewable`; stated ranges carry their
  byte-extent guards; Integer `arithmetic()` with equality elimination;
  `close_invariants()` deriving an `Integer` ranking member; user-grade
  refusals through the resource tracker (`docs/internals/resource-tracker.md`);
  array facts surviving declarations, separate allocations and separate calls;
  a second universal `have` narrowing a stated range (was a binder-identity
  bug, fixed in 88b05d28).

## Where the search proof stands

`design/dfs-gaps/search_terminates_blocked.md` is the full C and sidecar at the
furthest point reached. Everything verifies except one loop-invariant bundle
member: the contract, memory safety of the walk, the quantified `next` bound
instantiated at `cur`, the early-`return` arm, `unmarked_point_update` applied
between `at(iter, visited)` and `visited` after the store, `unmarked_nonnegative`
(a third lemma, in that file, that verifies and should move into
`mdtests/unmarked_count_lemmas.md`), and the strict decrease. The open member is
re-establishing the quantified invariant about `next` — specifically its
`viewable` half — at the loop's back edge:

```text
loop invariant bundle leaf [UnclosedGoal]: goal: ∀k. (0 <= k ∧ k < n) ⇒ viewable(next[k..k+1]) at the back-edge snapshot
```

It was last run after 88b05d28; rerun it first, because a lot has landed since
(resource-tracker explanations, byte-interval framing, history-based load
equality) and the refusal may have moved.

## Gaps, ranked by proof text they cost (reductions in `design/dfs-gaps/`)

1. **A quantified fact cannot be transported to another program point**
   (`a_universal_fact_does_not_transport.md`). `transport` refuses a quantified
   proposition and a comparison (`unsupported proof operation transport`), so a
   quantified precondition reaches a loop body one cell at a time: an
   entry-snapshot `instantiate`, two `extract`s, a load-equality transport and a
   hand-written orientation flip — 19 lines per premise. Also: a top-level
   `transport` in a `preserve` body verifies while the same `transport` inside a
   `have` there is refused. **This is what blocks `search` now.**
2. **A `return` inside a loop body** (`return_inside_a_ranked_loop_body.md`).
   Not one of the loop rule's body endings. `branch { then { execute(); } else
   { } }` accepts a returning arm only when an unrelated current-snapshot fact
   is already in context; otherwise `branch did not verify as a checked
   preservation operation`, which names no goal, premise or target and carries
   the wrong tactic index. Fix the diagnostic first, then the rule.
3. **A fact about part of an array dies at a store outside that part.**
   `unmarked(visited, 0, i)` reads only cells below `i`, but Click records that
   it depends on the whole array, so `visited[i] = 1` discards it. The user pays
   with the frame lemma plus a quantified per-cell transport: about 110 of the
   190 lines of the sweep example. A read-only design proposal exists
   (scratch, not in the repo): derive the read range from a fold-shaped function
   definition (`(lo..hi).fold` whose body reads `v[k]` at exactly the binder;
   anything else falls back to the whole array), carry it on the array argument,
   and let the resource tracker's assumption-free walk decide that a store to
   `a[i]` misses `a[0..i)` because the stored index is the same term as the
   range's upper bound. A too-small range is a false theorem, so the derivation
   must be default-deny. Not approved by the user yet — ask before building.
   It would not help `search` itself (there the store is inside the range and
   `unmarked_point_update` is genuinely needed).
4. **No gate-checked shared lemma library for mdtests.** `import` supplies
   theorem statements and assumes their proofs by design, and nothing in
   `scripts/check.sh` selects a library `.click` file, so `unmarked_frame` is
   copied verbatim (90 lines) into every example that needs it.
5. **Extent bounds restated at every pure-theorem `apply … using`.** A stated
   range carries `0 <= n - lo` and `n - lo <= 1073741823` for the proof, but a
   `using` list inside a pure theorem must name them again (the C-proof route
   already accepts a cited range's available guards). That checker promises to
   read only listed premises, so this is a design question.
6. Small ones (`small_refusals_and_spellings.md`): no `!=` symmetry (`y != x`
   from `x != y`), which forces `unmarked_point_update` to split its agreement
   premise into `below`/`above` — not re-tested on current master; `have` cannot
   take a label, so long quantified facts are written twice; `assumption()`
   cannot close a `viewable` goal; `arithmetic() using { j < hi; hi <= n }` will
   not weaken to `j <= n` and says the premises are insufficient;
   `missing pure fact: constant condition is true` does not say which constant;
   a store refusal spells `owns b[0..1]` as `owns a[(v100001 - v100000)..]`.

## Later stages

- A modest correctness claim for the iterative search (`result == 1` only via
  the `cur == to` exit), then real reachability, which needs a recursive pure
  function over an array (pure recursive functions use `fuel: Nat` today) or a
  model-based route: wrap the graph in a resource whose field is a pure model
  and state the measure on the model. The model route exposed its own gaps
  earlier (a loop guard cannot read a cell owned by a folded resource; no
  spelling for a model field at the head of an iteration).
- The recursive, branching DFS (`visited` plus two successor arrays).

## Rules of engagement that have worked

- Simple tactics first; smart tactics only once the explicit proof works.
- A refusal that does not say what is missing in source spelling is a bug in
  the refusal: fix the standard diagnostic, never add temporary debug output.
- Reduce every gap to a few-line reproduction before proposing a rule; each
  language addition gets its own minimal mdtest, reviewed by the user.
- This example sits on top of kernel memory reasoning that was under active
  soundness repair in September 2026 (see `docs/internals/memory-dag.md`,
  `docs/internals/resource-tracker.md`, `docs/internals/kernel.md` "Index and
  offset arithmetic"). Anything that verifies and should not is a stop-and-report
  event, ahead of any feature work.

## Acceptance

- `mdtests/search_terminates_by_unmarked_count.md` verifies termination and
  memory safety of the unmodified C above, with `unmarked_nonnegative` moved
  into the lemmas file.
- Each gap above that is fixed has a minimal regression mdtest; gaps that are
  deliberately left are recorded in the docs, and `design/dfs-gaps/` is deleted
  with this issue.
- A correctness claim for `search` is stated and proved, or the missing language
  support is split into its own issue at the user's request.
