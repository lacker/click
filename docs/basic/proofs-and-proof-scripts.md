# Proofs and proof scripts

A Click contract says what must hold. Its proof clause says how Click should
establish it.

Use an omitted proof clause or `by auto;` by default. `auto` orchestrates C
execution, effect reasoning, and proposition reasoning, and retains a checked
certificate when it succeeds.

Prefer smart tactics while authoring unless profiling identifies a hotspot.
Exact `using` blocks are ordinary Click and may be committed after expansion,
but manually listing every premise is not the normal starting workflow.

Click also has two single-purpose proof sugars:

- `by simp;` simplifies the goal at the current proof state.
- `by frame;` performs contextual frame reasoning at the current proof state.

Neither one executes C. For a whole-function proof, use `by auto;` or make the
sequence explicit:

```click
ensures result == x by {
    execute();
    simp();
}
```

```click
mutable p[0..n] by {
    execute();
    frame();
}
```

## Smart and simple tactics

Smart tactics may inspect context or search. The most common are bare
`step()`, `execute()`, `execute_until(...)`, `summarize(...)`, `simp()`, bare
`frame()`, bare `apply(...)`, and bare `transport(...)`.

Simple tactics perform one explicit rule. Paired operations use `using` to
mark that boundary:

```click
step() using {
    x < 2147483647;
}

summarize(loop(0)) using {
    n >= 0;
}

frame() using {
    i >= 0;
    i < n;
}
```

An empty `using {}` block is valid. It means the simple rule needs no pure
premises; it is not the same spelling as the contextual bare tactic.

Other common simple proposition tactics are `assumption()`, `normalize()`,
`rewrite(...)`, `intro()`, `split()`, `left()`, `right()`,
`contradiction(...)`, and `derive using { ... }`.

## Pure and execution proofs

A pure proof reasons at one program point. Pure theorems and nested
`have P by { ... }` proofs cannot execute C or transform resources. They can
use simplification, theorem application, exact derivation, logical tactics,
and proof-level `if`.

An execution proof carries a C frontier. The execution vocabulary is:

- `step()` for one smart transition;
- `execute_until(point)` for a forward prefix;
- `execute()` for the remainder of the function;
- `summarize(loop(N))` for one verified loop summary; and
- `reach(point) ensuring { ... } by { ... }` for a scoped execution proof that
  exports an explicit interface.

Proof-level `if` splits reasoning; it does not execute a C `if`. `reach` joins
scoped proof paths at a declared program point and forgets facts/resources not
listed in its interface.

## Expansion and diagnosis

`click expand` replaces a selected smart tactic with its checked simple
certificate. `click profile` identifies slow tactics and distinguishes smart
automation from simple leaves. `click audit` checks that smart tactics across a
project expand and replay successfully. Use this workflow only after the
selected proof is correct: expansion is a checked optimization, not a way to
extract a partial result from a proof whose later tactics fail.

The [proof tactics reference](../proof-tactics.md) is the exhaustive inventory
and compatibility guide.
