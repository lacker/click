# Proofs and proof scripts

A Click contract says what must hold. Its proof clause says how Click should
establish it.

Use an omitted proof clause or `by auto;` by default. `auto` orchestrates C
execution, effect reasoning, and proposition reasoning through checked proof
operations.

Prefer smart tactics while authoring unless profiling identifies a hotspot.
Exact `using` blocks are ordinary Click and may be committed after expansion,
but manually listing every premise is not the normal starting workflow.

Click also has two single-purpose proof sugars:

- `by simp;` simplifies the goal at the current proof state.
- `by frame;` performs contextual frame reasoning at the current proof state.

Neither one executes C. For a whole-function proof, use `by auto;` or make the
sequence explicit:

<!-- verified-example: mdtests/pure_theorem.md -->
```click
ensures result == x by {
    execute();
    simp();
}
```

<!-- verified-example: mdtests/pure_theorem.md -->
```click
mutable p[0..n] by {
    execute();
    frame();
}
```

## Smart and simple tactics

Smart tactics may inspect context or search. The most common are bare
`step()`, `execute()`, `execute_until(...)`, `simp()`, bare
`frame()`, bare `apply(...)`, and bare `transport(...)`.

Simple tactics perform one explicit rule. Paired operations use `using` to
mark that boundary:

<!-- verified-example: mdtests/pure_theorem.md -->
```click
frame() using {
    i >= 0;
    i < n;
}
```

An empty `using {}` block is valid. It means the simple rule needs no pure
premises. `step()` takes no `using` block: it is simple, and executes the
next statement with the whole proof context visible to the kernel.
`execute()` and `execute_until(statement(N))` are its repetitions; expansion
replaces them with the corresponding sequence of `step();` tactics.

`simp() using { ... }` is still smart: the listed facts restrict its search,
and expansion replaces it with named simple rules. Common simple proposition
tactics are `assumption()`, `normalize()`, `rewrite(...)`, `intro()`,
`split()`, `left()`, `right()`, and `contradiction(...)`. A successful
expansion contains only those explicit rules and named theorem applications.

## Pure and execution proofs

A pure proof reasons at one program point. Pure theorems and nested
`have P by { ... }` proofs cannot execute C or transform resources. They can
use simplification, theorem application, exact derivation, logical tactics,
and proof-level `if`.

An execution proof carries a C frontier. The execution vocabulary is:

- `mark name;` to name the current state for later `at(name, ...)` expressions;
- `step()` for one smart transition;
- `execute_until(statement(N))` for a forward prefix;
- `execute()` for the remainder of the function;
- `branch { [ensuring { ... }] then { ... } else { ... } }` for the C `if` at
  the frontier and its single joined continuation; and
- `loop { ... }` for the C loop exactly at the current frontier.

Proof-level `if` splits reasoning; it does not execute a C `if`. Frontier-local
`branch` temporarily proves both C arms and then restores one current state.
A mark remembers a state the proof has already reached; it does not move the
frontier and is not an `execute_until` target.

## Expansion and diagnosis

`click expand` replaces a selected smart tactic with a checked explicit proof.
`click profile` identifies slow tactics and distinguishes smart automation from
simple leaves. `click audit` checks that smart tactics across a project expand
into source that verifies normally. Use this workflow only after the
selected proof is correct: expansion is a checked optimization, not a way to
extract a partial result from a proof whose later tactics fail.

The [proof tactics reference](../reference/tactics/index.md) is the exhaustive inventory
and compatibility guide.
