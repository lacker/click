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

`auto` is Click's default smart tactic. It symbolically executes the C function,
checks generated obligations, and searches the proof rules that are currently
available. For pure theorem declarations, `auto` proves the theorem goal
directly from the theorem's proposition requirements.

## Tactics

The current top-level tactics are:

```click
by auto;
by simp;
by frame;
```

Use `auto` for most beginner proofs.

Use `simp` for local simplification and contextual reasoning, especially after
unfolding a predicate. `simp` is classified as smart because it may combine
several reasoning rules even though its implementation is deterministic.

Use `frame` for `immutable` and `mutable` effect clauses.

Pure proofs for theorem declarations currently support `auto`, `simp`, and
proof-step scripts made from `unfold(name);`, `apply(theorem(args));`,
`assumption();`, `normalize();`, `rewrite(equality);`, and `simp();`.
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

An explicit script records a specific proof path, but not every current command
is simple. `assumption`, `normalize`, `rewrite`, and exact-premise `apply` are
simple tactics. `auto` and `simp` are smart tactics. Some execution and resource
commands remain fuzzy while their implicit reasoning is split into simple
rules. The [proof tactics reference](../proof-tactics.md) classifies every
command.

Common steps include:

- `step();`: perform one simple C statement transition using exact execution
  prerequisites and without automatic fact transport.
- `execute_step();`: execute one supported straight-line C statement from the
  current execution point using contextual prerequisite and automatic
  transport reasoning. It is smart automation over the explicit statement and
  fact-transport rules.
- `execute_rest();`: execute symbolically from the current execution point to
  function exit. From function entry, this executes the whole C function.
- `symbolic_execute();`: deprecated source alias for `execute_rest();`; both
  spellings parse to the same proof step.
- `execute_until(statement(N));`: advance from the current execution point to
  a forward, reachable statement entry point. An unresolved branch still
  requires explicit arm selection.

- `unfold(name);`: open a named predicate.
- `unfold(resource);`: expose one body layer of an owned composite resource.
- `fold(resource);`: rebuild one owned composite resource from its body.
- `apply(theorem(args));`: use a verified stdlib or current-file theorem as a
  derived fact. Its premises must be exact available facts or normalize to true.
- `observe(resource);`: expose one view layer of a held composite resource
  without unfolding its contained permissions.
- `simp();`: simplify the current proof goal.
- `assumption();`: close the current pure goal using an exact available fact.
- `normalize();`: close the current pure goal by context-free normalization.
- `rewrite(equality);`: perform one explicit equality substitution in the
  current pure goal.
- `transport(source, target);`: apply one explicit frame-transport theorem
  between memory snapshots.
- `frame();`: prove an effect claim.

Use `defined(expression)` to state expression safety explicitly. For example,
a theorem can derive `defined(x + 1)` from `x < 2147483647`; after applying that
theorem, `step()` can execute `return x + 1` without contextual search.

The end of the `by { ... }` block checks the claim.

For proofs that refer to a region more than once, attach a stable label with a
structural clause such as `for statement(4) as update { ... }`, then write
`execute_until(update)` and `at(update.entry, expression)`. Numeric statement
IDs are global source-preorder IDs and remain useful for declaring the label.

Existential proofs also use:

- `witness(k = expr);`: prove an existential by giving a value.
- `choose(k from requirement name);`: open an existential requirement.

## What To Read First

If you are reading a basic Click file, start with the contract and ignore the
proof script until you know what the guarantee says.

Then read the proof clause:

- `by auto` means the proof is automated.
- `by simp` means the result should follow by simplification.
- `by { ... }` means the author wrote an explicit proof script; consult its
  commands to see whether it is simple, smart, or still fuzzy.

The full proof-step reference is in the proof workflow page.
