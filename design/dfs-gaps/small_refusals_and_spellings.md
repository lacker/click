# small gaps found while proving the marking search

The int32 disequality symmetry refusal is resolved by
`mdtests/int32_disequality_symmetry.md`. The `below`/`above` split in the
point-update theorem remains necessary to cover indices on both sides of the
updated cell. The mdtest shared-library gate described below is also resolved;
`mdtests/unmarked_count_lemmas.click` is checked as an entry module.

Each of these cost one to six lines of proof text. None blocks a stage on its
own; together they are most of the bookkeeping in
`mdtests/unmarked_count_lemmas.md` and
`mdtests/sweep_maintains_a_zero_unmarked_count.md`.

## A cited range's extent halves are restated at every `apply`

Classification: **missing rule** (or a deliberate cost worth revisiting).

`docs/concepts/viewability.md` says a stated range carries its extent half
beside its viewability half, and that is true for the theorem's own proof: no
`have 0 <= n - lo` is needed anywhere in the lemmas now. But every application
still owes both halves *by name*:

```text
`unmarked_frame.ensures_0` proof step proof tactic 8: `apply` of the induction
hypothesis failed: instantiated premise `0 <= (n - lo) is true` does not follow
from the listed evidence
```

and for a theorem rather than the hypothesis, in the better wording:

```text
theorem `unmarked_frame` requirement 6 `viewable(a[lo..n])` states a memory
range, so applying it needs that range to be a valid 32-bit byte extent here:
`0 <= (n - lo) is true` is not an available fact. A range's extent is
`(end - start) * width` in 32-bit arithmetic, and without that bound it can wrap
to fewer bytes than its element count names
```

Both refusals are actionable without reading kernel code. The cost is six
`using` lines in the lemmas file and four in the sweep, for a fact the clause
three lines above already carries; a `views` premise could plausibly bring its
extent halves with it into an application the way it brings them into a proof.

## `arithmetic() using` will not weaken a bound it just derived

Resolved by `mdtests/arithmetic_weakens_transitive_bound.md` and the direct
one-step uses in `mdtests/unmarked_count_lemmas.click` and
`mdtests/branching_graph_dfs.md`. The refusal below is historical.

`j < hi` and `hi <= n` give `j < n`, which is `j <= n - 1`, so `j <= n`
follows. The planner refuses it in one step:

```text
`unmarked_point_update.ensures_0` proof step proof tactic 1 > have body tactic
1: current goal does not follow from exactly the listed arithmetic premises
(exactly the listed premises were insufficient)
```

Written as two steps — `have j < n` then `have j <= n by { arithmetic() using
{ j < n; } }` — it goes through. One extra line per occurrence.

## A constant-true requirement instance must be `have`d before it is cited

Resolved by `mdtests/apply_using_accepts_a_constant_true_premise.md`: a listed
premise that lowers to the constant it asserts (`0 <= 0` at `lo = 0`) needs no
fact. A constantly false one still refuses and now names the listed premise in
the proof's spelling (`mdtests/apply_using_names_a_false_constant_premise.md`);
it used to say only `missing pure fact: constant condition is true`.

## `assumption()` does not close a `viewable` goal

Does not reproduce on master: `assumption()` closes a `viewable` goal from the
identical fact established by `transport ... using`, from a `both` arm and
under a universal, through the same exact indexed lookup as any other goal.
`mdtests/assumption_closes_an_established_viewable_fact.md` pins it; a wider
range or another snapshot still refuses
(`mdtests/assumption_does_not_close_a_viewable_goal_at_another_range.md`,
`mdtests/assumption_does_not_close_a_viewable_goal_at_another_snapshot.md`).
The original `close_invariants by` arm was not rebuilt: a loop invariant
`viewable(a[0..i])` is refused at the loop head for its unsigned extent bound.

## The owned range in a store refusal is spelled against the wrong base

Resolved by `mdtests/a_store_refusal_names_the_stores_own_base.md`. With
`views a[0..n]; owns b[0..n];` the store to `b[0]` was refused as missing
`owns a[(v100001 - v100000)..]`: every external pointer shares one block, and
the first parameter was used as the base. The refusal now spells the range
against the parameter it sits at a constant offset from (`owns b[0..1]`) and
notes that the held `owns b[0..n]` covers it only when `1 <= n`.

## A `have` cannot carry a label

Classification: **missing surface spelling**, cosmetic.

`requires below: forall (...) { ... }` labels a premise, and `choose(name from
requirement(label))` reads one, but `have below: P by { ... }` is a parse
error:

```text
line 19, column 24: expected comparison operator in `proposition`, got Colon
```

In a proof with two structurally similar quantified frame facts, a label would
be how the later `using` list said which one it meant; instead both are written
out in full, twice, at fourteen lines each.

## Theorem proofs cannot be shared between mdtests

Classification: **missing tooling** (not a language gap).

`import "other.click";` exists and works —
`mdtests/specification_imports.md` is the fixture — but
`docs/concepts/sidecars.md` is explicit that "An import provides declarations,
not a request to run proofs", and `verify_c0_project` "Verifies exactly the
proofs owned by a loaded entry module. Imported theorem statements and
declarations are available as conditional interfaces, but their proof bodies
are not executed." `scripts/check.sh` runs `cargo test --test mdtests`, which
selects only each `.md` file's own click block, so nothing in the gate ever
selects a `mdtests/*.click` library.

Verified directly: a library containing

```click
theorem library_claim(x: int32) {
    requires 0 <= x;
    requires x < 100;
    ensures x == x + 1 by { simp(); }
}
```

is imported and applied by an mdtest that then passes (`x == x + 1` is false;
its body was never run). That is the documented selection boundary rather than a
soundness hole, but it means a shared lemma
file in `mdtests/` would be an *unchecked* assumption for every file that used
it. So `unmarked_frame` is a verbatim ninety-line copy in each of the two
examples that need it, and `unmarked_point_update` and `unmarked_nonnegative`
would be two more, and the cost of the campaign's central lemma is paid once
per file.
