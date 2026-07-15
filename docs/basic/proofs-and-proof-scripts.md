# Proofs And Proof Scripts

A Click contract says what should be true. A proof clause says how Click should
prove it.

Click distinguishes **pure proofs** from **execution proofs**. A pure proof
derives propositions from facts at one program point. An execution proof moves
forward through a code region, relating its entry state and resources to its
exit state and resources. A function proof is an execution proof; a pure
theorem proof has no C execution frontier.

The simplest proof clause is:

```click
by auto;
```

`auto` is Click's default automation. It symbolically executes the C function,
checks generated obligations, and tries the deterministic proof rules that are
currently available. For pure theorem declarations, `auto` proves the theorem
goal directly from the theorem's proposition requirements.

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

Pure proofs for theorem declarations currently support `auto`, `simp`, and
proof-step scripts made from `unfold(name);`, `apply(theorem(args));`, and `simp();`.
They do not run C execution steps because there is no C function body attached
to the theorem, and they do not run resource steps because theorem application
does not change the resource context.

## Proof-Step Scripts

When a proof needs more control, write a proof-step script:

```click
ensures result == x by {
    execute_rest();
    simp();
}
```

Proof steps are meant to be stable and replayable. They are less magical than
`auto`: the script records a specific proof path. Execution steps advance the
execution frontier. Pure steps such as `apply` and `simp` derive facts without
advancing it; resource steps can transform resource facts at the current
frontier.

Common steps include:

- `execute_step();`: execute one supported straight-line C statement from the
  current execution point.
- `execute_rest();`: execute symbolically from the current execution point to
  function exit. From function entry, this executes the whole C function.
- `symbolic_execute();`: legacy spelling for `execute_rest();`.
- `execute_until(statement(N));`: advance from the current execution point to
  a forward, reachable statement entry point. An unresolved branch still
  requires explicit arm selection.
- `unfold(name);`: open a named predicate.
- `unfold(resource);`: expose one body layer of an owned composite resource.
- `fold(resource);`: rebuild one owned composite resource from its body.
- `apply(theorem(args));`: use a verified stdlib or current-file theorem as a
  derived fact.
- `observe(resource);`: expose one view layer of a held composite resource
  without unfolding its contained permissions.
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
