# Canonical pointer offsets need a production invariant

## Violated invariant

Production evaluation must never place a `Bitvector32Term::MemoryLoad` inside
pointer-offset arithmetic. A loaded pointer or index must first be named by a
canonical variable with a defining fact, keeping snapshots in the proof
context rather than in the small terms compared by alias and order reasoning.

The canonicalization landed in `canonicalized_pointer_value_from_int_cell`
and `canonicalized_symbolic_load_value`, and the motivating corpus is green.
What is missing is a structural regression over pointers produced by the real
evaluation/lowering entry points. Kernel tests that deliberately construct a
raw load-bearing offset are not violations of this production boundary.

## Intended regression

Evaluate representative loaded pointer/index expressions through the
production APIs, recursively walk every resulting `PointerOffsetTerm`, and
fail if any reachable `Int32Scaled.value` contains a `MemoryLoad`. Include at
least a loaded array index and a pointer loaded from an opaque cell.

## Acceptance criteria

- The regression observes production-generated values, not hand-normalized
  expected terms.
- Every load used in pointer arithmetic is a canonical variable and its
  defining equality is present in the emitted facts.
- No C source, tactic budget, or verifier limit changes.
- This file and its Open-list line are deleted when the regression and any
  necessary canonicalization fixes land under a green `scripts/check.sh`.
