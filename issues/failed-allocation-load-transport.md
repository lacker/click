# Preserve loads across failed-allocation refinement

## Problem

The null branch of `malloc` is semantically memory-preserving, but resolving a
pending allocation to failure removes it from the kernel's pending-allocation
map without recording a memory-derivation edge. Memory snapshots on the two
sides therefore have different heap metadata and no certified connection.

Owned-vector growth exposed this when proving that allocation failure leaves
the old live prefix unchanged. Click retained the complete old-buffer
loadability fact, yet could not lower a quantified postcondition for one cell
because its address used the post-refinement snapshot.

## Invariant

Every modeled memory-state transition must either:

- record the exact cells/ranges/lifetime it may change; or
- record that it changes no program-observable memory.

A failed allocation changes no program-visible storage. Load and loadability
transport may cross that refinement for every existing pointer, while still
keeping the symbolic malloc result constrained to null and producing no
allocation resources.

## Regression

Allocate a fresh runtime-sized buffer while owning a separate existing array.
On the null branch, prove a quantified equality between every existing array
cell and its function-entry value. Include a success branch showing that the
new allocation remains fresh and uninitialized rather than being conflated
with failure.

## Acceptance criteria

- Failed-allocation refinement records a replayable memory derivation.
- Existing loads and loadability facts transport across its null branch.
- No allocation authority or memory resource is produced on failure.
- Successful allocation, uninitialized-read rejection, and allocation
  freshness remain unchanged.
- The owned-vector failure branch proves content preservation without a
  redundant C write or a proof-only snapshot workaround.
