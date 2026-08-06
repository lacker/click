# Eliminate the specialized vector-push C clone

## Problem

The owned-vector example once called `vector_push` from its pipeline. It was
changed to `vector_push_first`, and the repository now contains two nearly
identical C implementations:

- `vector_push` for an allocation-owning `allocated_vector`;
- `vector_push_first` for an empty vector over caller-supplied storage.

The distinction belongs to Click's resource boundary, not to the append
algorithm. Cloning and renaming the C function let each copy have one easier
contract, but it does not demonstrate that Click can specify the existing
general append operation in different valid ownership contexts.

## Source-fidelity invariant

One C function should not need proof-specialized clones merely because callers
package the same memory with different resource states or lifetime authority.
Click must express reusable behavior around the implementation that exists.

## Design work

Determine the smallest general mechanism that lets the unchanged
`vector_push` implementation support both contexts. Plausible designs include:

- a resource-neutral core contract over the required metadata and capacity
  ranges, with Click theorems or wrapper specifications that preserve the
  caller's enclosing resource;
- multiple verified contracts for one C body, provided their effect and safety
  judgments are independently kernel-checked; or
- a general composite-resource transition that carries optional allocation
  authority without duplicating the C function.

Do not solve this by keeping two source copies, adding a C wrapper whose only
purpose is contract selection, or weakening the allocated-vector lifetime
guarantee.

The resource-neutral core pattern is sufficient for the surface proof, and
recent frame-planning work keeps its relative backing-range check below the
smart-tactic threshold. The remaining attempt is blocked in kernel contract
certification; see
[Certify a resource-neutral callee without global proof search](certify-resource-neutral-callee-without-global-search.md).
Do not resume example edits by restoring the stopped attempt until that focused
certification regression is green.

## Intended regression

Retain one ordinary in-capacity append body. Verify calls to that same function
from:

1. an empty caller-supplied vector transitioning to nonempty;
2. a nonempty caller-supplied vector;
3. an allocation-owning vector before and after growth.

Each call must preserve the old prefix, capacity, backing pointer, and whatever
allocation authority the caller already held.

## Acceptance criteria

- `vector_push_first.c` is removed and `vector_pipeline.c` calls the unchanged
  general `vector_push` implementation.
- The three ownership contexts above verify without C wrappers or cloned
  implementations.
- Resource and allocation authority cannot be forged or dropped between the
  context-specific Click specifications.
- The resulting mechanism is documented as a general contract/resource
  pattern, not a vector-specific kernel rule.
- Expansion, audit, profiling, and the default test suite pass.
