# Proof and contract certification repeat function execution

Click intentionally checks a proof-directed execution against an independent
kernel execution and later constructs the opaque contract rule. Current
pipelines can execute the same function body in proof replay, independent
claim certification, whole-certificate replay for smart scripts, and final
contract certification. Separate per-claim proofs can multiply the work by the
number of claims; bounded exact caches hide some repetitions but use deep keys
and do not establish a complexity bound.

`owned-segmented-buffer` is the current integration witness: its pipeline body
is the dominant operation and is genuinely executed twice across proof and
opaque-contract boundaries. Owned-string and binary-tree profiles show smaller
versions of the same aggregate cost.

## Required design

Define a kernel-owned checked execution artifact whose authority includes the
exact annotated function, entry state, assumptions, environment dependency
identity, execution semantics, and complete frontier. Proof/certificate replay
may refer to that artifact, but cannot manufacture it. Final contract
certification should validate the already checked artifact against the exact
contract boundary rather than rerun the body when all inputs coincide.

If independence requires two genuinely different judgments, make the second
one consume a compact derivation from the first so its work is proportional to
the certificate, not the C body. This is a proof-boundary design change and
must not be approximated with another ambient success cache.

## Regression design

Scale one straight-line function body while holding one grouped simple proof
fixed, then scale the number of claims over the fixed body. Count symbolic
statement transitions by phase. The body-size curve may have a small constant
certification multiplier; the claim-count curve must not multiply body
execution.

Keep `owned-segmented-buffer` as the integration profile after the reduced
regression is green.

## Acceptance criteria

- A function body is symbolically executed at most once per distinct exact
  execution judgment in an all-simple grouped proof.
- Adding claims does not re-execute the body.
- Smart whole-certificate replay checks certificate evidence without silently
  trusting search state.
- The independent kernel authority boundary is documented and regression
  tested.
- Owned-segmented-buffer gains comfortable deadline margin without budget or
  source changes.
