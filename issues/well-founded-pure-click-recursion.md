# Add well-founded recursion to pure Click functions

## Problem

Pure Click functions currently reject recursive call graphs. Unlike C
procedures, a pure Click function denotes a specification value: using it in a
postcondition, invariant, predicate, or theorem presumes that evaluation
produces a value. Partial correctness is therefore not an appropriate escape
hatch for recursive pure definitions.

The language needs recursive pure functions for inductive data summaries, but
accepting the C recursion rule here would make specification evaluation
nonterminating or logically inconsistent.

## Design

Recursive pure Click functions must be total. Require an explicit well-founded
measure for every function in a recursive call-graph component. A first version
should stay deliberately small:

```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}
```

The exact line-breaking and placement can follow the parser, but use the common
term `decreases`; do not invent a C-specific recursion keyword. For the first
slice, support one integer-valued natural-number measure. At each reachable
component-internal call edge:

- prove the callee's instantiated measure is nonnegative and strictly smaller
  than the caller's current measure; and
- reject arithmetic in the measure whose definedness cannot be established.

A base path that makes no recursive call need not prove that its unused
incoming measure is nonnegative. This lets `countdown` remain total on negative
`int32` inputs while giving every recursive chain a natural-valued descending
rank.

Mutual recursion should use the caller's current measure and the callee's
instantiated measure at each component-internal edge. Lexicographic tuples,
user-defined well-founded relations, and coinductive values can wait for a
demonstrated example.

Termination checking alone is not enough to make symbolic recursive functions
useful. Define the evaluation boundary explicitly:

- concrete arguments may unfold repeatedly while the measure decreases;
- symbolic calls should remain a recursive application unless a proof tactic
  deliberately unfolds one equation;
- unfolding exposes exactly one body equation and must not recursively
  normalize an unknown-depth structure; and
- proof induction over the measure is a separate capability if examples need
  properties beyond one-step unfolding.

This avoids replacing the current recursion rejection with evaluator budget
failures.

## Focused mdtests

- `pure_recursive_function.md`: a directly recursive function over a small
  natural argument evaluates on concrete inputs.
- `pure_recursive_function_unfold.md`: a symbolic call unfolds exactly one
  defining equation under the relevant branch condition.
- `pure_recursive_function_requires_decreases.md`: recursive definitions with
  no measure are rejected clearly.
- `pure_recursive_function_rejects_non_decrease.md`: a self-call with the same
  or larger measure is rejected.
- `pure_recursive_function_rejects_negative_measure.md`: a recursive edge to a
  negative next measure is rejected, while a negative nonrecursive base path
  remains valid.
- `pure_mutual_recursion.md`: an even/odd pair verifies with decreasing
  measures.
- `pure_recursive_function_in_invariant.md`: a terminating recursive summary
  can be mentioned in a loop invariant without eager infinite unfolding.
- `pure_recursive_function_in_resource_guard.md`: if allowed by the existing
  load-free guard restrictions, a one-step recursive summary behaves
  consistently during independent certification.

## Documentation

Update the pure-functions guide and language reference to contrast the two
models explicitly:

- recursive C contracts are partial by default and need no decrease;
- recursive pure Click functions must be total because they denote values; and
- `decreases` controls termination, while `unfold` controls proof-time
  visibility of a defining equation.

## Acceptance criteria

- Well-founded direct and mutual pure recursion is accepted.
- Missing or invalid decreases proofs fail during validation with an edge- and
  function-specific diagnostic.
- Symbolic evaluation never relies on a recursion-depth budget for soundness.
- One-step unfolding and independent certificate replay agree.
- Documentation does not imply that the C partial-recursion rule applies to
  value-level Click functions.
