# Recursion

Priority: P2.

Soundness: incomplete. The listed hard cases are rejected today with
diagnostics. None is accepted under a weaker termination argument.

This is the deferred hard-bucket issue for the remaining recursive C proof
shapes. The ordinary recursive contract rule and the first termination slices
already work; this issue collects the cases where recursion must compose with
resource transitions, loop joins, or more expressive well-founded measures.

## Supported baseline

Click currently supports:

- partial-correctness contracts for direct and mutual C recursion;
- numeric recursive components whose functions use one unchanged `int32`
  parameter and pass a smaller value by a positive constant decrement;
- direct and mutual recursion ranked by expression measures: any pure
  `int32`, unsigned, 64-bit, or `Integer` expression, a bare non-`int32`
  parameter, or a lexicographic tuple of them, each call within the
  component owing the callee's measure nonnegative and lexicographically
  below the caller's entry reading;
- guarded direct structural recursion over a recursive composite resource,
  including consuming or mutating the resource during an ordinary recursive
  traversal and postorder deallocation;
- count-up, lexicographic, and separately ranked nested loop measures;
- numeric recursive calls inside ranked loops when the loop ranking and the
  function-level ranking are independently checked;
- read-only direct-child structural recursion inside a ranked loop;
- recursive calls inside ranked loops whose descent depends on the loop's
  changing counters, ranked by a function-level expression or tuple measure
  and discharged from the loop invariants
  (`mdtests/c_decreases_lexicographic_recursion_under_loops.md`).

These behaviors have checked positive and negative regressions. They should
remain unchanged while the hard cases below are added.

## Remaining hard cases

### Resource transitions inside ranked loops

A structurally decreasing recursive call that consumes or mutates a child
resource inside a ranked loop still cannot cross a continuing loop back edge.
The next iteration must receive exactly the surviving resource populations,
allocation authority, and heap lifetime required by its invariant. The proof
must never recover a consumed child or hide a mutation behind the loop join.

### Mutual structural recursion over a model-free resource

A resource with a `match model` body ranks mutual structural recursion through
a `decreases t` binder measure, checked at each call against the entry model
(`mdtests/c_decreases_binder_measure_mutual_recursion.md`), or through an
expression measure over the model such as `decreases links_len(x.model)`
(`mdtests/c_decreases_model_measure_mutual_recursion.md`). An `if`-guarded
resource without a model, measured by `decreases list(node)`, still supports
only direct self-recursion: its analysis reads the body for a direct child, and
there is no model for a call-ranked check to compare. Mutual resource-definition
cycles remain a separate resource-algebra concern.

## Intended regressions

Use unchanged C fixtures and checked sidecars for each slice:

1. A finite ranked loop calls a structural recursive helper that consumes or
   mutates a child and then continues. A positive case must preserve the
   residual resource state; a negative case must show that a freed or consumed
   child cannot be resurrected at the loop join.
2. Mutually recursive C functions descend through guarded structural resource
   children. Parent, unrelated-child, and unguarded edges remain rejected.

## Acceptance criteria

- Every supported recursive shape has a kernel-checked termination derivation;
  no surface plan, hidden body rerun, C rewrite, or execution budget stands in
  for the derivation.
- Resource-consuming or mutating recursive calls that continue through a loop
  preserve exactly the allowed resource, allocation, and heap state, with no
  ownership duplication or resurrection.
- Structural mutual recursion checks the guarded well-founded relation and
  direct child ancestry for every edge.
- Combined caller/callee measures and richer function-level measures check
  their arithmetic, well-foundedness, substitutions, and address-escape
  conditions on all reachable edges.
- Positive and negative regressions cover each supported slice, the hard-case
  boundary remains precisely diagnosed, and `scripts/check.sh` passes.

Split a subproblem into its own issue if implementation work establishes that
its semantics or acceptance criteria are genuinely independent.
