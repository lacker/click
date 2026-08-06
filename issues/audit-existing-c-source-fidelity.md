# Audit examples against unchanged existing C

## Problem

Most Click examples were authored together with their proofs. They are useful
feature fixtures, but verifier-friendly synthetic C is weak evidence for
Click's main adoption claim: proving properties of existing code that cannot be
refactored around the verifier.

History already contains source changes coupled to proof repairs, including a
weakened owned-string pipeline, a no-op allocation branch, specialized vector
push code, helper rerouting in the input-cursor pipeline, and local-variable
renames. The focused issues beside this one repair the known cases; there may be
others whose intent is not visible from the current tree.

## Source-fidelity invariant

An integration fixture claimed as existing or realistic C must preserve the
source behavior that motivated it. A passing proof of a rewritten program does
not close the original Click gap.

## Audit work

Review the history of every modified `examples/**/*.c` file and classify each
change as one of:

1. independently desired program behavior;
2. an actual C bug or undefined-behavior fix;
3. documented semantics-preserving C0 desugaring; or
4. verifier-motivated source adaptation.

Restore category 4 changes or create a focused issue that retains the original
source pattern. Do not infer legitimacy merely because the current C is
reasonable.

Then add a small provenance-preserving fixture class for code imported from an
existing project. Record the upstream source and revision, keep the imported C
unchanged, and place all Click-specific material in sidecars or build metadata.
A manifest or test should make accidental source edits visible without making
intentional upstream refreshes impossible.

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
- The five known source-fidelity issues in `issues/README.md` are resolved.
- At least one nontrivial multi-function fixture preserves identifiable
  existing C source and verifies without proof-oriented edits.
- Provenance and source-integrity checks run in the normal test workflow.
- The example documentation does not use synthetic, simplified C as evidence
  that unchanged real-world C is supported.
- The contributor workflow explains how to reduce failures while preserving
  the original semantic pattern.
