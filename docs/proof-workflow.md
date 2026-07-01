# Proof Workflow

Click proofs live in `by` clauses.

## Tactics

Currently accepted tactics:

```click
by auto;
by simp;
by frame;
```

Omitting a proof clause uses `auto`.

`auto` is the broad orchestration tactic. It runs the current symbolic
execution, loop-VC, effect-checking, simplification, and bounded-execution
fallback paths as needed.

`simp` is deterministic local normalization. It is useful for straight-line
postconditions and unfolded predicate goals. It simplifies logical connectives,
constant/reflexive integer comparisons, small arithmetic forms, concrete folds,
and several kernel equality patterns.

`frame` proves `immutable` and `mutable` effect clauses. It rejects ordinary
postconditions.

## Proof-Step Scripts

Deterministic proof scripts use function-call-shaped proof steps:

```click
by {
    symbolic_execute();
    unfold(sorted);
    simp();
}
```

Current proof steps:

- `symbolic_execute();`: build symbolic verification paths for the C0 function.
- `bounded_execute();`: use deterministic bounded execution for concrete-loop
  fallback proofs.
- `loop_vc(loop(N));`: check the generated verification conditions for loop
  code region `N`.
- `frame();`: prove the current function-level effect claim.
- `frame(loop(N));`: prove the effect summary for loop code region `N` and
  expose it for later postcondition reasoning.
- `unfold(name);`: unfold matching predicate facts and goals.
- `apply(theorem_name(args...));`: instantiate a verified pure theorem from the
  standard library or current file, prove its requirements from the current
  proof context, and add its conclusions as derived facts.
- `choose(k from requirement name);`: open a named existential precondition,
  introducing proof-local int32 value `k`.
- `choose(k from requirement N);`: the same operation by zero-based requirement
  index. Prefer labels for durable scripts.
- `witness(k = expression);`: prove the current existential goal by substituting
  the given int32 expression for binder `k`.
- `simp();`: request deterministic simplification when the proof block is
  checked.

The end of a `by { ... }` block checks the overall claim.

Some successful `auto` proofs record replayable proof-step certificates when the
current proof-step language can express the argument.

Existential proof steps are deterministic replay steps, not search tactics. A
typical existential-introduction proof names a witness:

```click
ensures found: (0..n).any(|k| { k == result }) by {
    symbolic_execute();
    witness(k = 0);
    simp();
}
```

`choose` is existential elimination for facts that are already assumed. The
current source forms are intentionally narrow: `requirement name` means a
`requires name: ...;` label, while `requirement N` means the Nth written
`requires` clause. The selected source must lower to an existential
proposition, either directly or after an explicit `unfold(predicate);` step.

```click
requires has_k: exists (int32 k) { k == x };
ensures again: exists (int32 j) { j == x } by {
    symbolic_execute();
    choose(k from requirement has_k);
    witness(j = k);
    simp();
}
```

For a predicate requirement that hides an existential, unfold the predicate
first:

```click
requires has_x: bytes_contains(p, 0, n, 'x');
ensures again: bytes_contains(p, 0, n, 'x') by {
    symbolic_execute();
    unfold(bytes_contains);
    choose(found from requirement has_x);
    witness(k = found);
    simp();
}
```

## Structural Blocks

Structural proof blocks attach facts to code regions:

```click
for statement(2) {
    assert i == 0 by auto;
}

for loop(0) {
    invariant i >= 0 by auto;
    invariant i <= n by auto;
    mutable p[0..n] by frame;

    step {
        mutable p[i..i + 1] by frame;
    }
}
```

`statement(N)` selects the Nth source statement code region in structural
order. `loop(N)` selects the Nth `while` loop code region. A code region may
also be labeled with `as name` and used in proof steps such as `frame(name)`.

A code region is a static source construct with extent, such as a function,
loop, statement, or block. A program point is a proof-relevant boundary or
position in the program, often associated with a code region, such as
`loop_name.entry`. A visit is one runtime arrival at a program point. Visits
are useful semantic language, but they are not currently Click syntax.

Snapshot expressions use visit selectors:

```click
at(function.entry, x)
at(loop_name.entry, x)
```

The initial `loop_name.entry` support is limited to invariants on that same
labeled loop code region.

`assert` is a one-shot spec check at the selected statement code region. It
currently accepts the executable proposition fragment over current-state C
fragments.

`invariant` generates obligations at loop program points: before the first
visit to the loop body, when one body visit preserves the invariant, and at loop
exit. Invariant proof blocks can use `by auto;` or an unfold-only script such
as:

```click
by {
    unfold(sorted);
    unfold(sorted_range);
}
```

Full proof-step scripts for invariant entry and preservation are not separate
surface proof blocks yet.

## Loop Effects

Whole-loop effects:

```click
for loop(0) {
    mutable p[0..n] by frame;
}
```

Step-relative effects:

```click
for loop(0) {
    step {
        mutable p[i..i + 1] by frame;
    }
}
```

Whole-loop mutable segments must use stable names such as parameters. They
cannot depend on locals modified by the loop. Use `step` effects for
iteration-relative footprints.

Loop effect summaries are reusable. For example, if a loop mutates only
`dst[0..n]` and requirements prove `disjoint(dst[0..n], src[0..n])`, `auto` can
use that effect summary to prove source-memory postconditions without a
handwritten source-invariance invariant.

## Debugging Failed Proofs

Failure messages usually include:

- guarantee label
- execution path index
- available requirements
- path facts
- remaining proof obligations
- simplified proposition for failed `simp`

Practical approach:

1. Find the failing mdtest and the exact guarantee label.
2. Read path facts to learn which branch/path failed.
3. If a predicate is still opaque, add `unfold(predicate_name);`.
4. If memory preservation is missing, check `valid_range`, `disjoint`,
   `immutable`, `mutable`, and loop effects.
5. If arithmetic overflow appears, add numeric requirements or invariants.
6. If the proof needs a general new pattern, add a focused mdtest and then a
   deterministic kernel/proof rule.
