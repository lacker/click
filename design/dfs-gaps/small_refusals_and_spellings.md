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

Classification: **missing rule**, small.

Applying a theorem at `lo = 0` owes `0 <= lo`, which at that instance is
`0 <= 0`. Naming it in the `using` list is refused:

```text
`search.contract` tactic 2: `apply using` requires an exact premise: missing
pure fact: constant condition is true
```

`have 0 <= 0 by { simp(); }` fixes it. The message does not say *which*
constant condition it wanted, which is the only reason it took a guess to
repair: with four constants in one `using` list it names none of them.

## `assumption()` does not close a `viewable` goal

Classification: **missing rule**.

A `viewable` fact established by `transport ... using` does not close the
identical `viewable` goal:

```text
`assumption` requires the current goal as an available semantic fact: current
goal is a memory-viewability fact
```

So a narrowing has to be the *last* tactic of its `have` body, closing the goal
directly with `simp()`, rather than being established and then cited. In a
`both { ... }` arm of a `close_invariants by` bundle, where the goal is handed
to the arm, that leaves no way to finish.

## The owned range in a store refusal is spelled against the wrong base

Classification: **bad diagnostic**.

With `views a[0..n]; owns b[0..n]; requires 0 <= n;` — where `n` may be `0`, so
a store to `b[0]` really is unjustified — the refusal is:

```text
`walk.contract` tactic 0: `step()` produced runtime error: missing resource
fact `owns a[(v100001 - v100000)..((v100001 - v100000) + 1)]`
```

The verdict is right and the spelling is not. The store is to `b[0]` and the
resource it needs is `owns b[0..1]`; instead the reader is shown the same bytes
expressed as an offset from the *other* parameter's base, with two kernel
variables in it. `docs/internals/resource-tracker.md` promises the opposite —
"It spells the resource with the user's own names (`a[m]`, `g[0]`)" and "An
index only the lowering has a name for is printed `a[…]`, never as the kernel
variable". It also does not say the interesting part, which is that `n` may be
zero.

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
