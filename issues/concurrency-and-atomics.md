# Model concurrency and atomics

C0 has no threads, synchronization, atomics, fences, or data-race model.

## Violated invariant

Click should not certify a concurrent C program using sequential reasoning that
can hide a data race, reorder an atomic access, or miss a synchronization
failure.

## Intended regression

An unchanged two-thread C fixture uses an atomic counter and a release/acquire
flag. A race-containing variant must be rejected, while the synchronized
variant receives a contract whose memory observations match the selected memory
model.

## Acceptance criteria

- The supported memory model, atomic orders, thread creation/join, and race
  diagnostics are documented and represented in the kernel.
- Proof rules prevent sequential proofs from being reused across unsound
  concurrent transitions.
- The synchronized and racy regressions pass; `scripts/check.sh` passes.
