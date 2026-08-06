# Add the first unchanged existing-C fixture

## Problem

Most Click examples were authored together with their proofs. They are useful
feature fixtures, but verifier-friendly synthetic C is weak evidence for
Click's main adoption claim: proving properties of existing code that cannot be
refactored around the verifier.

History contained source changes coupled to proof repairs, including a
weakened owned-string pipeline, a no-op allocation branch, specialized vector
push code, helper rerouting in the input-cursor pipeline, and local-variable
renames. The post-introduction C history has now been classified below. All
known workarounds except the specialized vector push have been restored.

The remaining larger gap is that every current example is synthetic. Even the
`jsonc-refcount` pilot is json-c-shaped code authored in this repository, not
an upstream import. The tree therefore has no source-integrity fixture that
supports Click's unchanged-existing-C adoption claim.

## Source-fidelity invariant

An integration fixture claimed as existing or realistic C must preserve the
source behavior that motivated it. A passing proof of a rewritten program does
not close the original Click gap.

## Completed historical audit

| Change | Classification | Current status |
| --- | --- | --- |
| owned-string pipeline replaced push/get/pop with clear and `return first` | verifier-motivated adaptation | original modular pipeline restored in `07bed24` |
| allocator wrapper added a null self-assignment branch | verifier-motivated adaptation | natural wrapper restored in `888b8f2` |
| input-cursor's second independent initialization was rerouted through clone | verifier-motivated adaptation | independent initialization restored in `a273fd2` |
| `result` locals were renamed to avoid a lowering collision | verifier-motivated spelling adaptation | original names restored in `c32c8bd` |
| general `vector_push` was renamed and specialized for the first element | verifier-motivated helper specialization | still open in `use-general-vector-push-in-pipeline.md` |
| owned-string pop became a real general pop; vector fill became owner-based; list destruction became ordinary `void` recursion | independently desired example/API changes | retained and documented by their feature commits |
| vector pipeline moved from inline mutations to ordinary API calls; arbitrary-index vector set replaced the fixed-index helper | independently desired strengthening | retained as harder, more representative fixtures |
| linked-list empty changed from an integer-shaped placeholder to a null pointer constructor | actual C type/behavior correction | retained |

Newly added C files are synthetic fixtures by construction. Their subsequent
edits were reviewed through `git log -- examples/**/*.c`; no other unresolved
proof-motivated source adaptation was found.

## Remaining fixture work

Add a small provenance-preserving fixture imported from an existing project.
Record the upstream source and revision, keep the imported C unchanged, and
place all Click-specific material in sidecars or build metadata. A manifest or
test should make accidental source edits visible without making intentional
upstream refreshes impossible.

## Documentation and workflow

Document the distinction between:

- synthetic examples that isolate one language feature;
- semantics-preserving C0 transcriptions whose differences are recorded; and
- unchanged existing-source fixtures that support the adoption claim.

Proof failures in the third class must produce Click regressions or issues,
never silent source edits.

## Acceptance criteria

- Every historical modification to an example C file has a recorded
  classification, with verifier workarounds restored or separately tracked.
- The specialized vector-push source-fidelity issue is resolved.
- At least one nontrivial multi-function fixture preserves identifiable
  existing C source and verifies without proof-oriented edits.
- Provenance and source-integrity checks run in the normal test workflow.
- The example documentation does not use synthetic, simplified C as evidence
  that unchanged real-world C is supported.
- The contributor workflow explains how to reduce failures while preserving
  the original semantic pattern.
