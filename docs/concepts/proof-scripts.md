# Proofs and proof scripts

A Click contract says what must hold. Its proof clause says how Click should
establish it.

Use an omitted proof clause or `by auto;` by default. `auto` orchestrates C
execution, effect reasoning, and proposition reasoning through checked proof
operations.

Prefer smart tactics while authoring unless profiling identifies a hotspot.
Exact `using` blocks are ordinary Click and may be committed after expansion,
but manually listing every premise is not the normal starting workflow.

Click also has one single-purpose proof sugar:

- `by simp;` simplifies the goal at the current proof state.

It does not execute C. For a whole-function proof, use `by auto;` or make the
sequence explicit:

<!-- verified-example: mdtests/pure_theorem.md -->
```click
ensures result == x by {
    execute();
    simp();
}
```

## Smart and simple tactics

Smart tactics plan or search. The most common are `execute()`,
`execute_until(...)`, `simp()`, bare `apply(...)`, and bare `transport(...)`.

Simple tactics request one deterministic checked operation without planning or
search, and their checkers must be fast and output-sensitive. Paired operations
use `using` to mark that boundary:

<!-- verified-example: mdtests/pure_theorem.md -->
```click
simp() using {
    i >= 0;
    i < n;
}
```

An empty `using {}` block is valid. It means the simple rule needs no pure
premises. `step()` is simple and executes the next statement with the whole
proof context visible to the kernel.
`execute()` and `execute_until(statement(N))` are its repetitions; expansion
replaces them with the corresponding sequence of `step();` tactics.

`simp() using { ... }` is still smart: the listed facts restrict its search,
and expansion replaces it with named simple rules. Common simple proposition
tactics are `assumption()`, `normalize()`, `rewrite(...)`, `intro()`,
`split()`, `left()`, `right()`, and `contradiction(...)`. A successful
expansion contains only those explicit rules and named theorem applications.

## Pure, fixed-state, and execution proofs

A pure proof reasons without a symbolic C state. A fixed-state proof reasons
against one fixed symbolic C state but does not advance execution. Pure
theorems use pure proofs; nested `have P by { ... }` proofs use fixed-state
proofs. Both can use simplification, theorem application, exact derivation,
logical tactics, and proof-level `if`; fixed-state proofs can additionally
transform logical resources.

An execution proof carries a C frontier. The execution vocabulary is:

- `mark name;` to name the current state for later `at(name, ...)` expressions;
- `step()` for one simple deterministic transition;
- `execute_until(statement(N))` for a forward prefix;
- `execute()` for the remainder of the function;
- `branch { [ensuring { ... }] then { ... } else { ... } }` for the C `if` at
  the frontier and its single joined continuation; and
- `loop { ... }` for the C loop exactly at the current frontier.

Proof-level `if` splits reasoning; it does not execute a C `if`. Frontier-local
`branch` temporarily proves both C arms and then restores one current state.
A mark remembers a state the proof has already reached; it does not move the
frontier and is not an `execute_until` target.

## Splitting a model by constructor

`match value { Type::Variant(fields) => { ... } ... }` splits an execution proof
into one arm per constructor, with the constructor equation and fresh field
bindings on each arm's path. It may run at any frontier the proof has reached:
at unchanged function entry, after executed statements, and inside a loop's
`preserve` body.

<!-- verified-example: mdtests/proof_match_after_c_step.md -->
```click
step();
match c.model {
    Maybe::None => { contradiction(c.model == Maybe::None); },
    Maybe::Some(value) => {
        unfold(c);
        execute();
        let c = fold(cell(node), { model: Maybe::Some(value) });
        simp();
    },
}
```

Where the arms end depends on the region. In a function proof each arm runs to
function exit and the arms are joined there. In a loop's `preserve` body each
arm runs to the loop's back edge and the arms are not joined at all, because a
preservation path never joins across it — see
[Opening a binder's model inside the body](loops-and-invariants.md#opening-a-binders-model-inside-the-body).

The constructor equation is an entry assumption of the whole function only when
the `match` ran before any C step. At a later frontier it holds on that arm's
path from the split onwards.

## Naming a call result

C often uses a call's result without ever storing it: `if (f(x))` and
`return f(x);` both leave the callee's guarantee and the branch or return
fact attached to a value the proof has no word for. The call step's existing
`let` binder names it. On a callee that declares a `produces` binder the `let`
introduces that instance; on a callee that declares none it names the call's
scalar result:

<!-- verified-example: mdtests/call_result_in_condition.md -->
```click
let r = step(classify(x), { });
```

`r` is then an ordinary value name in `have`, `rewrite`, `normalize() using`,
and `simp` premises, on both sides of the `branch` that spells the C `if`. It
denotes the value the call returned, so it keeps its meaning after later
statements. Naming the result of a call whose result the C discards is an
error, as is reusing a name that is already a C local or a proof-local
binding. `examples/modeled-binary-tree` uses this to prove
`ensures result == heap_member(old(t.model), target);` for the recursive
`tree_contains`, whose two recursive calls appear only in a condition and a
return expression.

## Expansion and diagnosis

`click expand` replaces a selected smart tactic with a checked explicit proof.
`click profile` identifies slow tactics and distinguishes smart automation from
simple leaves. `click audit` checks that smart tactics across a project expand
into source that verifies normally. Use this workflow only after the
selected proof is correct: expansion is a checked optimization, not a way to
extract a partial result from a proof whose later tactics fail.

The [proof tactics reference](../reference/tactics/index.md) is the exhaustive inventory
and compatibility guide.
