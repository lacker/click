# Model function pointers

C0 has no function-pointer type, address-of-function expression, indirect call,
or callback contract. Callback resources model proof-side capabilities, not C
function pointers.

## Violated invariant

Click should preserve the target and call-target semantics of C callbacks,
including compatible signatures and any lifetime or provenance restrictions.

## Intended regression

An unchanged C file declares a comparator function, passes its address through a
function-pointer parameter, and calls it indirectly. A negative test rejects an
incompatible function-pointer assignment and an indirect call with a positioned
diagnostic until the model exists.

## Acceptance criteria

- Function-pointer types and compatible signatures are represented in the
  surface and kernel.
- Indirect calls retain a checked target set and do not invent a body or
  contract for an incompatible target.
- The callback regressions pass; `scripts/check.sh` passes.
