# Verify a pointer-chasing search over an index array (the "DFS" example), and the soundness findings it exposed

P1. Two things live here, because they came out of one campaign and the second
blocks trusting the first:

- **Part 1** — the DFS forcing-function example and the language gaps it found.
- **Part 2** — kernel soundness findings that are still open. Per
  `issues/README.md`, an unsound rule is P1 whatever it is about, and these come
  before feature work. Everything a new agent needs is in this file and in
  `design/dfs-gaps/`; nothing depends on anyone's scratch files.

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
  `next` (its `viewable` half) at the loop's back edge. Rerun it first; a lot of
  kernel work has landed since it was last run and the refusal may have moved.
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

## Open — false theorems with a witness on master

### S1. A local's address outlives its scope

```c
int32 f(int32 n) {
    int32* q; int32 z;
    if (n == 0) { int32 a[2]; a[0] = 5; q = &a[0]; } else { int32 b[2]; b[0] = 5; q = &b[0]; }
    z = q[0];            /* dangling in C */
    return z;            /* `ensures result == 5` verifies */
}
```

Also verifies for: nested `if` scopes, a `while` body local read after the loop
(including after `break`), a `switch` case local, a `for`-init variable read
through a pointer after the loop, and an arm local's address stored in a struct
field. `mdtests/automatic_block_reentry_lifetime_alias.md` states the intended
verdict (`undefined behavior: invalid memory access`) for the re-entry variant.

Cause: the surface proof stepper never executes an `if` as a unit —
`execute_branch_step_from_frontier_position`
(`src/surface/proof/cursor_execution.rs`) splices the selected arm in front of
the `if`'s tail, so there is no step at which the arm is left and nothing ends
the arm's locals. The kernel's own executors do retire a scope's locals at every
exit (`end_scope_automatic_lifetimes`, `paths_after_scope_exit`, landed in
b99f30c0 with five kernel tests), but no sidecar proof goes through that route,
so the witness above still verifies.

Fix shape: a recorded execution event, `CheckedAutomaticLifetimeEnd
{ before_state, after_state, blocks }`, modelled on `CheckedResourceObservation`
(`src/kernel/proof/execution.rs`), recorded where the stepper leaves a region
(the `exited_branch_regions(...)` sites), including `break`/`continue`/`return`
out of an arm. A silent state change is rejected by the proof object
("evidence does not start from the running state") — that was tried. `for`-init
variables are lowered as a sibling of the loop (`src/languages/c/syntax.rs`), so
they need a frontend scope or the same event keyed on the `for` region.

Related, not exploitable from a caller today: a non-inline callee body that is
executed in place never retires its locals or its `local:frame:` parameter slots
(`src/kernel/functions.rs`, `end_inline_frame_automatic_lifetimes` runs only for
inline bodies), so such a callee can certify `ensures *out[0] == 3` about its own
local. Retiring parameter slots must wait until postconditions have been read
(struct-by-value `ensures` read them).

### S2. A contract whose own clauses alias under its `requires`

```c
int32 aliased(int32* p, int32* w) { int32 t; w[0] = 7; t = p[1]; return t; }
```
```click
int32 aliased(int32* p, int32* w) {
    requires w == p + 1;
    requires p[1] == 3;
    views p[0..3];
    consumes w[0..3];
    ensures result == 3;          // verifies; the C returns 7
} by { execute(); simp(); }
```

`w[0]` is `p[1]`. The entry fact "a contract's owned and viewed clauses are
separate" (`contract_entry_partition_facts`, `src/kernel/functions.rs`) frames the
store away. No ordinary caller can enter (the stable-view planner refuses every
call that satisfies the `requires`), and a recursive self-call only re-enters the
same context, so this is a vacuous contract rather than an escape — but Click
issues a verified claim about real C that is false under a satisfiable `requires`.
The guard exists and fires for `requires w == p`
("the contract's `views` clause overlaps its own `owns` clause"), not for
`w == p + 1`: `install_borrowed_contract_inputs` (`src/kernel/api.rs`) strips
memory separations and asks `protected_range_proven_overlapping`
(`src/kernel/loans.rs`), whose cross-base route does not spend the `requires`
pointer-offset equality to place `w`'s range against `p`'s. That is the repair.

### S3. A symbolic resource count can still wrap

Constant totals are now exact (`population_quantity_sum`; regression
`mdtests/a_population_count_is_not_a_wrapped_total.md`, which refuses
`produces k of tok(o)` twice at `k == 2000000000` proving `count(tok(o)) < 0`).
Two gaps remain underneath: `c_counted_population_transition`'s ledger update
`prior + (ensured - required)` is still a modular add, and the merge of a symbolic
quantity with a constant `1` (`own_quantity(R, n) + own(R)`, the shape every
refcount contract uses) is kept unguarded on purpose. Closing both means carrying
`0 <= q <= i32::MAX` with every population quantity. The refusal for the symbolic
case is also unusable: `claim Ensure(2) on path 0 has mismatched proposition
completion evidence` (`src/surface/proof/claim_proofs.rs`).

## Open — unsound or unexamined reasoning, no witness yet

Ranked by how likely a witness is.

1. **A call's or loop's write set carries no widths.** `Proposition::CMemoryMutatesOnly`
   holds `pointers: Vec<Pointer>` only, the branch join in
   `src/kernel/proof/execution.rs` unions arm writes and drops widths, and the
   consumers — `c_memory_load_is_directly_unchanged`'s `CMemoryMutatesOnly` arm
   (`src/kernel/memory_provenance.rs`, including a plain
   `pointer_byte_offset_from_base != 0` rung) and
   `memory_snapshots_directly_proven_equal_for_memory_resolution`
   (`memory_conditions.rs`) — frame a write away from a read on address
   inequality alone. Attack: a callee whose `mutable` clause writes an `int64` at
   `q` while the caller keeps a fact about the `int32` at `q + 4`. Gating with the
   widest scalar for both sides would make every `a[i]`/`a[j]` pair `Unknown` and
   kill array framing, so the fix needs real widths: derive the write width by
   diffing the effect's two snapshots, carry it in the proposition (~30 sites), or
   thread the load width through the four call sites. When gating a ladder, call
   the explicit-range rung beside the gate, not under it — gating it away once
   cost +545% work on `rb_replace_node_with_children`.
2. **`resolve_memory_load_value`** (`memory_conditions.rs`) has no width parameter
   and returns the stored value of a pointer-equal cell whatever width that cell
   holds, so a 2-byte stored value can answer a 4-byte load. Narrow and cheap to
   attack. Also `heap_allocation_may_contain_pointer`'s `base.block !=
   pointer.block` test is fail-open on a block spelling.
3. **`separate(memory(a[s..s + 2]), …)` with `s` unconstrained is accepted**, where
   `owns a[s..s + 2]` would owe `not signed_add_overflows`. A provably reversed
   range is refused; an undecided one is not
   (`mdtests/an_ordinary_separation_clause_needs_no_extent_text.md` pins this
   limit). It could not be made an obligation because a range reached through a
   composite resource publishes no extent guard to its user, and half of the
   guard is an unsigned comparison the surface cannot write. Prerequisite:
   composites publish their inner ranges' guards in the signed count spelling
   (`memory_range_element_count_guards`).
4. **The load-side distinct-cell reduction names a load at an ancestor snapshot**
   using the current path's facts (`evaluate_c_memory_load_paths_with_alias_cache`,
   `src/kernel/eval/memory_loads.rs`); 369 refused backwards `CellsForgotten`
   edges over the corpus come from it. Argued benign (every step skipped is a
   store it proved distinct; names are assumption-free), and one attack on name
   reuse across branch arms was refused — but it is fact-dependent naming on the
   hottest path and deserves a second attack.
5. **Snapshots unrelated by recorded history are still compared by cell maps**
   (`memories_match_for_pointer_load`); the doc comment says what that rests on
   (equal havoc markers, extents, observable cells). No path between them exists
   for the history to speak about.
6. `one_element_gap_separates_bytes` decides a *direction* from residue indexes
   (the `Separate` answer does not depend on it); `range_fold`'s one-step shortcut
   (`term_operations.rs`) uses a wrapping add (`i32::MAX .. i32::MIN` unrolls
   once) — judged unreachable because `(a..b).fold` lowers to the signed Integer
   carrier.
7. Probed once and found sound (18 sidecars, no false theorem): `uint32`
   arithmetic and order, signed/unsigned comparison, shifts by ≥ width,
   `INT_MIN % -1`, `uint32`→`int32` conversion, `<` and `-` between pointers into
   different objects; `decreases` on a `uint32` is refused outright. Not modelled
   rather than unsound: `uint8`/`uint16` wrap on assignment (the true claim
   `result == 44` for `200 + 100` is refused too), and the narrowing refusal exits
   as `type mismatch` instead of the message its own mdtests pin. `int8` is not in
   the subset.
8. Trust-model notes, by design rather than bugs: the `apply` tactic's
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
