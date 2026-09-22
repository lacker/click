# Verify a pointer-chasing search over an index array (the "DFS" example), and the soundness findings it exposed

P1. Two things live here, because they came out of one campaign and the second
blocks trusting the first:

- **Part 1** — the DFS forcing-function example and the language gaps it found.
- **Part 2** — kernel soundness findings that are still open. Per
  `issues/README.md`, an unsound rule is P1 whatever it is about, and these come
  before feature work. Everything a new agent needs is in this file and in
  `design/dfs-gaps/`; nothing depends on anyone's scratch files.

## Handoff checkpoint — 2026-09-21, after the quantified-viewability fix

The loop back edge's quantified viewability obligation for `next` now closes.
`mdtests/loop_quantified_viewability_across_disjoint_store.md` is the minimal
regression. The saved DFS proof was rerun unchanged: it advances past that
leaf and now stops at the value half of the same quantified invariant, while
the nonnegative count and strict-decrease facts remain available. This is a
normal proof failure, not a timeout.

This is **not yet a routine cleanup handoff**:

- The remaining Part 2 snapshot/aliasing items are investigations, not confirmed
  false-theorem witnesses or implementation plans. The unrelated-snapshot
  comparison needs careful semantic reasoning; retain experienced review for
  its conclusion and any kernel changes.
- The remaining DFS blocker concerns transporting the quantified value fact
  across the loop-entry and iteration-entry snapshots. The viewability half is
  covered by the regression above; do not conflate the residual value failure
  with it.
- Moving an already verified lemma into the checked lemma fixture, refreshing
  old reproductions, and reducing a diagnostic are bounded tasks suitable for
  a less capable agent. Whole-array dependency refinement, reachability, and
  recursive DFS remain design work, not small finishing edits.

For a bounded next assignment, reduce the new quantified-value leaf in
`design/dfs-gaps/search_terminates_blocked.md`, identifying why the available
iteration-entry invariant is not selected for the loop-entry load snapshot.
The remaining Part 2 audits still precede resuming feature implementation.

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
`docs/concepts/viewability.md`. The fold-read-range design in Part 1 item 3
still needs discussion before implementation. No scratch files or conversation
history are required to reproduce the current blocker.

---

# Part 1 — the DFS example

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
  `search` at the furthest point reached. Everything verifies except one
  loop-invariant bundle member: re-establishing the quantified invariant about
  `next` (now its value half) at the loop's back edge. The generated quantified
  viewability member closes first and is regression-covered. Rerun the saved
  proof first; the refusal may move as transport work lands.
  It also holds a third lemma, `unmarked_nonnegative`, that verifies and should
  move into `mdtests/unmarked_count_lemmas.md`.

## Gaps, ranked by the proof text they cost (reductions in `design/dfs-gaps/`)

1. **A quantified fact cannot be transported to another program point**
   (`a_universal_fact_does_not_transport.md`). `transport` refuses a quantified
   proposition and a comparison (`unsupported proof operation transport`), so a
   quantified precondition reaches a loop body one cell at a time — 19 lines per
   premise. A top-level `transport` in a `preserve` body verifies while the same
   `transport` inside a `have` there is refused. **This blocks `search`.**
2. **A `return` inside a loop body** (`return_inside_a_ranked_loop_body.md`).
   `branch { then { execute(); } else { } }` accepts a returning arm only when an
   unrelated current-snapshot fact is already in context; otherwise
   `branch did not verify as a checked preservation operation`, which names no
   goal, premise or target and carries the wrong tactic index. Fix the
   diagnostic first, then the rule.
3. **A fact about part of an array dies at a store outside that part.**
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
4. **No gate-checked shared lemma library for mdtests.** `import` supplies
   theorem statements and assumes their proofs by design, and nothing in
   `scripts/check.sh` selects a library `.click` file, so lemmas are copied
   verbatim into each example.
5. **Extent bounds restated at every pure-theorem `apply … using`.** A stated
   range carries `0 <= n - lo` and `n - lo <= 1073741823` for the proof, but a
   `using` list in a pure theorem must name them again (the C-proof route accepts
   a cited range's available guards). That checker promises to read only listed
   premises, so this is a design question.
6. Small ones (`small_refusals_and_spellings.md`): no `!=` symmetry (forces
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

## Acceptance (Part 1)

`mdtests/search_terminates_by_unmarked_count.md` verifies termination and memory
safety of the unmodified C; each fixed gap has a minimal regression mdtest; a
correctness claim is proved or split out at the user's request;
`design/dfs-gaps/` is deleted with this issue.

---

# Part 2 — open soundness findings

## How they were found, and how to find more

Every finding below came from taking a rule that "looked wrong but had no known
witness" and attacking it with a few-line C sidecar. About twenty false theorems
were found and fixed this way in September 2026; in that period no item classed
"latent" survived an attack as merely latent. Work attack-first: write the
witness, confirm it verifies on master, fix at the root, keep the witness as an
`expect fail:` mdtest. A guard that merely happens to sit elsewhere is not a
soundness argument — the rule must require its own premise.

Recurring roots worth auditing by name:

- **R1** an `int32` constant read as unsigned (`Bitvector32Term::as_const` is
  `u32`) and then ordered. The blessed signed reader is
  `signed_bitvector_constant` (`docs/internals/kernel.md`).
- **R2** wrapping 32-bit index arithmetic read as mathematical. Index terms are
  modular; pointer byte offsets are exact `i64` (same doc, "Index and offset
  arithmetic").
- **R3** "addresses differ" used where "byte intervals are disjoint" is needed.
  The one helper is `access_byte_overlap` (`Overlaps | Separate | Unknown`).
- **R4** absence of a cached cell read as "nothing was written". Cell maps are
  incomplete by design; the recorded history is the authority
  (`recorded_load_history`, `docs/internals/memory-dag.md`).
- **R5** block *names* compared instead of `PointerBlock::proven_distinct`.
- **R6** fresh identifiers drawn from a range the producer does not own (range
  registry in `docs/internals/kernel.md`).
- Control-flow walks (`switch`/`break`) that silently stop checking the rest of a
  function (`walk_termination_paths`).

Cost evidence must be deterministic work from `click profile`; wall-clock on the
development machine varies by ±50% run to run.

## Fixed soundness findings

### S1. Automatic storage and logical aggregate parameter values

Surface scope exits, for-update ordering, callee body locals, and all parameter
storage now retire. Regressions live in `mdtests/automatic_scope_exit_*.md` and
`mdtests/aggregate_parameter_*.md`; valid paths and expansion are checked too.
Callee stores through caller-local pointers also refresh their named bindings.

The remaining witness from `076c7c5e` exported `&input.value` through an output
pointer and incorrectly verified `ensures *out[0] == 7`. It is now rejected.
Logical aggregate field projections retain parameter values independently of
C storage; they cannot grant access through an escaped pointer. Ordinary field
reads, nested and array fields, shallow pointer values, `old(...)`, and aggregate
returns have positive coverage. The restriction on postconditions reading
modified by-value parameter fields remains in place.

S2's offset-alias partition witness is rejected by indexed pointer and offset
equalities, with exact byte comparisons for concrete extents. Its regression is
`mdtests/contract_view_offset_alias.md`; negative offsets, mixed widths, adjacent
ranges, and indexed query scaling are checked in kernel/surface tests.

S3's symbolic count merges and call-ledger additions now require an established
no-overflow bound. The negative and bounded positive examples are
`mdtests/population_symbolic_increment_*.md`; the bounded example also expands
and rechecks. The earlier constant-total regression now names the population
count bound instead of reporting a certificate-completion mismatch.

Separation now carries shared range-validity bounds in both directions: a
premise supplies them, and a goal or call requirement must establish them.
Composite observation/unfolding exposes the bounds of its contained ranges.
`mdtests/separation_extent_*.md` cover unbounded and wrapping goals, bounded
calls, theorem premises/applications, and composite bounds; positive contracts
also expand and recheck. Symbolic bounds are compared with wide-integer
arithmetic at endpoint extremes for widths 1, 2, 4, and 8. The investigation
found an unchecked separation goal, but no accepted false return-value proof.

## Open — unsound or unexamined reasoning, no witness yet

Ranked by how likely a witness is.

The two width findings have been repaired: `CMemoryMutatesOnly` carries
`(Pointer, byte_width)` writes through joins and substitutions; framing and
mutable-footprint checks use complete byte accesses. Load-value resolution
requires the requested width to match the stored cell. Mixed-width effect and
load-resolution regressions are in the kernel memory-reasoning tests.
`heap_allocation_may_contain_pointer`'s block-spelling test remains unexamined.

4. **Snapshots unrelated by recorded history are still compared by cell maps**
   (`memories_match_for_pointer_load`); the doc comment says what that rests on
   (equal havoc markers, extents, observable cells). No path between them exists
   for the history to speak about.
5. `one_element_gap_separates_bytes` decides a *direction* from residue indexes
   (the `Separate` answer does not depend on it); `range_fold`'s one-step shortcut
   (`term_operations.rs`) uses a wrapping add (`i32::MAX .. i32::MIN` unrolls
   once) — judged unreachable because `(a..b).fold` lowers to the signed Integer
   carrier.
6. Probed once and found sound (18 sidecars, no false theorem): `uint32`
   arithmetic and order, signed/unsigned comparison, shifts by ≥ width,
   `INT_MIN % -1`, `uint32`→`int32` conversion, `<` and `-` between pointers into
   different objects; `decreases` on a `uint32` is refused outright. Not modelled
   rather than unsound: `uint8`/`uint16` wrap on assignment (the true claim
   `result == 44` for `200 + 100` is refused too), and the narrowing refusal exits
   as `type mismatch` instead of the message its own mdtests pin. `int8` is not in
   the subset.
7. Trust-model notes, by design rather than bugs: the `apply` tactic's
   requirement checks (including range extent guards) are enforced on the surface
   side at one shared point
   (`instantiate_theorem_application_with_assumptions`); a top-level `owns`/`views`
   range's extent at the program's outer boundary is an environment assumption;
   `import` assumes imported proofs.

## Tooling findings

- The CLI surface-depth boundary tests (`src/bin/click.rs`) run within 0.5% of
  the gate's 8 MiB stack: `CMemory` travels by value inside `Term`, so adding one
  word to a snapshot overflows them. Keep new snapshot fields behind an existing
  pointer.
- `cargo test --lib` (not the gate) fails
  `scaling_tests::targeted_simple_verification_does_not_verify_unrelated_theorems`
  when tests share a process; nextest's per-test processes hide it.
- Unit tests need `RUST_MIN_STACK=8388608` outside the gate.
- The C0 parser panics instead of refusing on `int32* tab[2];` at file scope
  (`src/languages/c/syntax.rs`, "validated global array element type").
- `have h.slot[0] == 5` about a pointer field of a local struct refuses with
  "the kernel lowering produced 0 paths"; `object(...)` is not accepted inside
  `separate(...)` nor for a file-scope struct.
- Diagnostics that name nothing: `(callee precondition): false = true`; "invalid
  memory access" for a dangling use (the tombstone knows the variable's name).

## Acceptance (Part 2)

Each open item above is either fixed with its witness as an `expect fail:`
mdtest, or shown sound with the argument written on the rule, and removed from
this file. New findings are added here only at the user's request.
