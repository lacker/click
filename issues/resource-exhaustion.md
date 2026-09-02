# Bound non-heap resource exhaustion

The current judgment models C memory safety and selected heap lifetime rules,
but not process stack depth, address-space exhaustion, or failure to allocate
stack/local storage. A proof can therefore establish the modeled behavior
without establishing that the process has enough physical resources to run it.

## Violated invariant

The verification result should state which resource-exhaustion behaviors are
covered and should not silently imply a guarantee about unmodeled machine
limits.

## Intended regression

Documentation names stack depth, address space, and local-storage exhaustion as
outside the current judgment. A future resource-bounded mode verifies a
recursion-depth and allocation budget, and rejects a fixture that exceeds it.

## Acceptance criteria

- The public proof contract clearly distinguishes modeled undefined behavior
  from host resource exhaustion.
- If a bounded mode is added, its limits are explicit, deterministic, and
  checked by the kernel rather than inferred from the verifier process.
- Documentation and the bounded/unbounded regressions pass;
  `scripts/check.sh` passes.
