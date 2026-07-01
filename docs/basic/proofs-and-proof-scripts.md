# Proofs And Proof Scripts

A Click contract says what should be true. A proof clause says how Click should
prove it.

The simplest proof clause is:

```click
by auto;
```

`auto` is Click's default automation. It symbolically executes the C function,
checks generated obligations, and tries the deterministic proof rules that are
currently available.

## Tactics

The current top-level tactics are:

```click
by auto;
by simp;
by frame;
```

Use `auto` for most beginner proofs.

Use `simp` for deterministic local simplification, especially after unfolding a
predicate.

Use `frame` for `immutable` and `mutable` effect clauses.

## Proof-Step Scripts

When a proof needs more control, write a proof-step script:

```click
ensures result == x by {
    symbolic_execute();
    simp();
}
```

Proof steps are meant to be stable and replayable. They are less magical than
`auto`: the script records a specific proof path.

Common steps include:

- `symbolic_execute();`: execute the C function symbolically.
- `unfold(name);`: open a named predicate.
- `simp();`: simplify the current proof goal.
- `frame();`: prove an effect claim.

The end of the `by { ... }` block checks the claim.

Existential proofs also use:

- `witness(k = expr);`: prove an existential by giving a value.
- `choose(k from requirement name);`: open an existential requirement.

## What To Read First

If you are reading a basic Click file, start with the contract and ignore the
proof script until you know what the guarantee says.

Then read the proof clause:

- `by auto` means the proof is automated.
- `by simp` means the result should follow by simplification.
- `by { ... }` means the author needed a specific deterministic sequence.

The full proof-step reference is in the proof workflow page.
