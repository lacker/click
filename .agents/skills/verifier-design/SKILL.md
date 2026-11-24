---
name: verifier-design
description: Place a proposed verifier change in the fast part or the slow part and check it against that part's cost rule. Use before proposing, implementing, or reviewing any change that makes the verifier do more work — new reasoning in the kernel, a new rule in `decide`, a new search in a tactic, a new index, or a change to how lowering or evaluation builds terms — and whenever a thread suggests "change the verifier so that it does X".
---

# Verifier design check

The rules are in `docs/internals/verifier-design.md`. Read it first. This
skill is the procedure for applying them.

Use **program point** for the location passed to `at`, **version point**
for a read's identity selected by the assumption-free memory walk, and
**recorded symbolic state** for an `ExecutionState` retained on a proof path.
A `SymbolicMemory` or `SharedMemory` value is a **memory state**, which can contain
partial or abstract information. See the vocabulary in
`docs/concepts/memory-model.md`.
Externally defined API symbols and opaque import-profile identifiers retain
their exact upstream names; do not rewrite frozen compiler artifacts.

## 1. Name the part

Find the part the change touches in the table in "The parts". Use the
"Vocabulary" table to translate a mechanism name (order walk, difference
graph, memory resolution, premise selection) into its part. If the change
touches more than one part, do this check for each.

## 2. Prefer the slow part

If the change adds reasoning, first try to place it in the slow part: a new
strategy in the search behind `close()`, its arithmetic engine, or the implicit closer, or a
search helper that fills
an argument a tactic already accepts. Put it in the fast part only when every
proof needs it on every step, and say why.

## 3. Check the rule

For a fast-part change, name for each read:

- the index it reads, and the key built from the operation's input;
- why no collection that grows with the program, path, facts, states, or
  resources is scanned, including facts related to the input;
- the scaling test: work at several sizes as unrelated input grows, and as
  related input grows (a longer chain, a larger class, more stores between
  two loads), measured in deterministic work units
  (`instrumentation::measure_deterministic_work`), not wall time.

For a slow-part change, name:

- the budget it runs under and its bounded failure message;
- what `click expand` writes in its place;
- the explicit syntax that lets an author write that result with no search.
  If it doesn't exist, adding it is part of the change.
- that every fact it cites or proves raises to a Surface AST that lowers back to it
  (`docs/internals/raise-lower-principle.md`). Never try candidate Surface forms and fall
  back; name the value where it is introduced or add the syntax.

For a change to lowering or evaluation in either part, name the facts it
reads and confirm each only refuses the term, discharges an obligation, or
adds a side fact, never changes the term produced
(`docs/internals/raise-lower-principle.md#lowering-is-fact-stable`). Run
`scripts/audit.sh fact-stability` before and after; the change adds no new
`differs` lines, and the report names any change in its `refused` and
`paths:N` counts.

## 4. Report the check

Begin the proposal, or the pull request description, with:

```text
Design check
- Part: <part> (fast | slow)
- Why this part: <one sentence>
- Fast: index and key per read; scaling test name and sizes
- Slow: budget; what expansion writes; explicit syntax
- Fact-stable: facts read during lowering and why none changes the term
- Failure: <what a miss or refusal says>
```

A change that can't fill in the fast or the slow line, or the fact-stable
line when it touches lowering, doesn't go in. Report
that to the user instead of implementing it.

## 5. Existing scans

If the change touches code listed in the operation audit ledger of
`docs/internals/verification-efficiency.md`, don't add another scan beside it. Either fix that
scan (index it, or move it to the slow part with an explicit form) or leave
it as it is and say so.

## 6. Keep the enforced boundary narrow

Ambient search views require `SearchPermission`, constructed only in
`surface::planning`. The Cargo build checks kernel dependencies and pins
diagnostic sampler callers in `build_support/search_boundary.rs`.
Do not fix a boundary failure by widening its allowance or relabelling a query
as upkeep. Failure messages use the capped diagnostic sampler, never an
ambient scan to compute an omitted count or select the ends. Move the search into planning or use `SelectedFacts::from_propositions` for
explicitly selected premises;
if a legacy API needs migration, describe that migration and test its boundary.
An indexed bucket is not explicit input. Loadability checking permits one
implicit fact per address shape and uses exact membership for stated goals;
do not recover a missed proof by enumerating an ambiguous bucket. Select its
source in planning, retain the explicit transport in expansion, and test both
exact hits and misses as the bucket grows.
Checked view queries also must not enumerate pointer representations or exact
alias lists. Use indexed class/storage coordinates and align a selected source
with the query; other representations belong behind `SearchPermission`. Grow
both affine classes and same-block alias stars in tests, including misses and
displaced accesses beside unrelated views.
Condition queries use indexed truth or singleton shape/variable buckets, never
scalar-class enumeration. Read-validity sources retain their type and state
checks; alternate-source search requires planner permission. Kept-frame raw
fallbacks use singleton base buckets, not whole-block scans or alias walks.
Grow source state buckets and unrelated retained ranges as well as aliases;
keep exact hits, stale-memory refusals and expansion-without-search coverage.
Order/overflow helpers use maintained direct extrema and strict-bound witnesses;
do not restore condition-side scans or symbolic order-component walks in
interval checking. Require explicit intermediate bounds for longer chains.
Constant equality evidence selects extrema or singleton symbolic sources;
anchored memory equality selects singleton endpoint sources, retaining the
existing state checks. Contiguous exclusion runs are maintained at admission,
not traversed at query time. Grow equality stars, symbolic order chains and
branches, and excluded-value runs, including hits, misses and branch isolation. Prepared access returns one
`SelectedMemoryAccess`, never a supplier iterator to resource checking. Failure
of its provenance, quantity or coverage check is final. Keep explicit footprint
composition separate, and grow overlapping supplier buckets on refusal as well
as success. Object-provenance lookup selects an indexed witness; it does not
filter its object bucket. Provenance/bounds fallbacks use singleton direct
aliases; framed pointer recovery requires a singleton full-pointer source.
Grow same-address state buckets and direct-alias stars, keeping exact class
hits and stale-read/bounds refusals.
Run the boundary regressions with `test(gate_tests::search_boundary::)` in the
fast-gate binary. This enforcement does not replace deterministic scaling tests.

## 7. Preserve branch contexts

Branching retains the parent `PureFactContext` and extends a cheap persistent
clone. Contexts only grow and fork: there is no fact withdrawal, and a
missing-premise control queries the context built without the premise. Opposite truth-value assumptions record
falsehood while retaining the original
condition and its indexes. Treat explicit context restriction separately from
branch undo.

## 8. Keep checking failures distinct from search exhaustion

Use `CheckingWorkScope` for migrated checked operations, with an allowance
measure derived from explicit input or produced state, never ambient fact count.
Add deterministic tests for one expensive check inside search and many cheap
checks exhausting search. Preserve the original tactic and whole-run charges;
nested scope measurements must not be added again to profile totals. A scope is
a containment guard, not permission to scan or a substitute for growth tests.
