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

Pure proofs for theorem declarations currently support `by auto;`, `by simp;`,
and explicit proof scripts made from `unfold(name);`, `apply(theorem(args));`
in either spelling, `assumption();`, `normalize();`, `rewrite(equality);`,
`simp();`, the structural logical rules `intro();`, `conjunction();`, `left();`,
`right();`, `double_negation();`, `vacuous();`, `contradiction(P);`, the atomic
theory rules `derive(P) using { ... }` and `calculate(P) using { ... }`, and
proof-level `if`. They do not run C execution steps because there is no C
function body attached to the theorem, and they do not run resource tactics
because theorem application does not change the resource context. `by frame;`,
`have`, `witness`, and `choose` are also rejected in a theorem proof.

## Explicit Proof Scripts

When a proof needs more control, write an explicit tactic script:

```click
ensures result == x by {
    execute_rest();
    simp();
}
```

An explicit script records a specific proof path, but not every current tactic
is simple. `assumption`, `normalize`, `rewrite`, `close_invariants`, and the
exact-premise `using` spellings of `apply`, `transport`, `step`, and
`apply_loop_summary` are simple tactics. `auto`, `simp`, `execute_step`,
`execute_then_step`, `execute_else_step`, `execute_rest`, `execute_until`,
`bounded_execute`, contextual `by frame`, and the bare spellings of `apply` and
`transport` are smart tactics. `have`, proof-level `if`, and `advance` are proof
control-flow tactics. The
[proof tactics reference](../proof-tactics.md) classifies every tactic and
lists every synonym.

Common tactics include:

- `step();`: perform one simple C statement transition using exact execution
  prerequisites and without automatic fact transport.
- `execute_step();`: execute one supported C statement from the current
  execution point using contextual prerequisite and automatic transport
  reasoning. At an `if`, it enters a uniquely determined arm. It is smart
  automation over the explicit statement and fact-transport rules.
- `execute_rest();`: execute symbolically from the current execution point to
  function exit. From function entry, this executes the whole C function.
- `symbolic_execute();`: legacy source spelling of `execute_rest();`; both
  spellings invoke the same tactic. Prefer `execute_rest()`.
- `execute_until(statement(N));`: advance from the current execution point to
  a forward, reachable statement entry point. An unresolved branch still
  requires explicit arm selection.

- `unfold(name);`: open a named predicate.
- `unfold(resource);`: expose one body layer of an owned composite resource.
- `fold(resource);`: rebuild one owned composite resource after its pure body
  facts have been established exactly.
- `apply(theorem(args));`: use a verified stdlib or current-file theorem as a
  derived fact. Its premises must be exact available facts or normalize to true.
- `observe(resource);`: expose one view layer of a held composite resource
  without unfolding its contained permissions.
- `simp();`: simplify the current proof goal.
- `assumption();`: close the current pure goal using an exact available fact.
- `normalize();`: close the current pure goal by context-free normalization.
- `rewrite(equality);`: perform one explicit equality substitution in the
  current pure goal.
- `transport(source, target);`: transport an exact fact between memory
  snapshots using certified execution effects. This covers framed conditions
  and structural memory facts such as `loadable(...)`.
- `frame();`: check a certified write summary against an effect claim using
  exact available range bounds. `by frame` is the smart contextual form.
- `close_invariants();`: discharge a loop's invariant bundle inside a
  `preserve by { ... }` proof.

Use `defined(expression)` to state expression safety explicitly. For example,
a theorem can derive `defined(x + 1)` from `x < 2147483647`; after applying that
theorem, `step()` can execute `return x + 1` without contextual search.

The end of the `by { ... }` block checks the claim.

For proofs that refer to a region more than once, attach a stable label with a
structural clause such as `for statement(4) as update { ... }`, then write
`execute_until(update)` and `at(update.entry, expression)`. In a proposition
position, the same selector can snapshot a complete claim:
`at(update.entry, loadable(p[0..n]))`. Numeric statement IDs are global
source-preorder IDs and remain useful for declaring the label.

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
  tactics to see whether each is simple, smart, or control flow.

The full tactic inventory, including which spellings are synonyms, is the
[proof tactics reference](../proof-tactics.md).
