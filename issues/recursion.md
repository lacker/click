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
- direct self-recursion ranked by an expression measure: any pure `int32`,
  unsigned, 64-bit, or `Integer` expression, a bare non-`int32` parameter,
  or a lexicographic tuple of them, each call owing nonnegativity and
  lexicographic descent against the entry reading;
- guarded direct structural recursion over a recursive composite resource,
  including consuming or mutating the resource during an ordinary recursive
  traversal and postorder deallocation;
- count-up, lexicographic, and separately ranked nested loop measures;
- numeric recursive calls inside ranked loops when the loop ranking and the
  function-level ranking are independently checked; and
- read-only direct-child structural recursion inside a ranked loop.

These behaviors have checked positive and negative regressions. They should
remain unchanged while the hard cases below are added.

## Remaining hard cases

### Resource transitions inside ranked loops

A structurally decreasing recursive call that consumes or mutates a child
resource inside a ranked loop still cannot cross a continuing loop back edge.
The next iteration must receive exactly the surviving resource populations,
allocation authority, and heap lifetime required by its invariant. The proof
must never recover a consumed child or hide a mutation behind the loop join.

### Mutual structural recursion

A structural `decreases` currently supports a guarded directly recursive composite
and direct self-recursive C calls. Mutually recursive C functions using
structural resource measures need a checked well-founded family rather than a
same-function direct-child rule. Mutual resource-definition cycles remain a
separate resource-algebra concern.

### Recursion under a changing caller measure

A recursive call whose descent depends on a caller's changing lexicographic
loop measure is currently rejected. Supporting it requires composing the
caller phase and callee descent without treating either measure as unchanged
across the other transition.

### Expression measures across mutual recursion

Expression and tuple measures rank direct self-recursion: the descent is owed
at a call to the function that declared the measure. A recursive component
with more than one function is refused by name, and `decreases <int32
parameter>` remains the only measure for it. Supporting it requires a
measure on every member, compared across members on each cross-function
edge (one shared carrier and tuple shape), with the same nonnegativity,
descent, and address-escape checks.

## Intended regressions

Use unchanged C fixtures and checked sidecars for each slice:

1. A finite ranked loop calls a structural recursive helper that consumes or
   mutates a child and then continues. A positive case must preserve the
   residual resource state; a negative case must show that a freed or consumed
   child cannot be resurrected at the loop join.
2. Mutually recursive C functions descend through guarded structural resource
   children. Parent, unrelated-child, and unguarded edges remain rejected.
3. A recursive call inside a loop descends using a changing caller tuple. The
   combined ranking must be checked on every recursive edge and loop back edge;
   a non-decreasing edge must fail.
4. Mutually recursive C functions each declare an expression or tuple
   measure, and every cross-function edge is checked for nonnegativity and
   strict descent; a deliberately non-decreasing edge is rejected.

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
