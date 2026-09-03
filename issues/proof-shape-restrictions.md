# Lift proof-shape restrictions that force restructuring

## Status

Direct `intro()` steps after execution reaches function exit now advance the
checked outcome proof. `instantiate using` is also available inside pure
theorem proofs. Both behaviors have regression coverage. The remaining
proof-shape restrictions below are still open.

Found by the 2026-09-01 kernel audit at cb034b21. Each bullet is a place
where a proof author must restructure a correct proof to satisfy the driver,
with no semantic reason.

- `choose` witnesses only int32 existentials
  (`src/surface/proof/proof_object/fixed_state_steps.rs:270-272` "only int32
  existential choices are supported"); existentials over pointers or other
  sorts must find another route.
- Grouped contract proofs forbid top-level `choose` and `witness`
  (`src/surface/proof/claim_proofs.rs:208-223`), forcing a `have` wrapper.
- Several shapes (heap-backed contract predicates, scopes nested in branch
  arms, quantified scope bodies) fall to a compatibility path or
  `unsupported_proof_shape` (`claim_proofs.rs:76-102`, `:429`, `:607`).
- `branch ensuring` can expose children of an unguarded composite only
  (`src/surface/proof/cursor_execution.rs:319-321`).
- Contract certification refuses requirements that lower to several paths
  unless one is selected or consistent
  (`src/kernel/api/contract_certification.rs:905-960`), and errors for any
  outcome other than Return or VerificationDiverges
  (`contract_claims.rs:901-934`).

## Violated invariant

The checked drivers should accept every proof the kernel can check, in the
shape the author naturally writes it, and every decline should name the
construct and the accepted alternative.

## Intended regression

One mdtest per remaining bullet showing the natural shape verifies:
`choose` on an `exists (p: int32*)`; top-level `choose` in a grouped contract
proof; a scope inside a branch arm; a guarded composite's child exported
through `branch ensuring`; and a contract with a conditional requirement.

## Acceptance criteria

- Each bullet either verifies in its natural shape or fails with a diagnostic
  naming the construct, the reason, and the rewrite, at the source position.
- The generic "proof shape is not accepted" message is gone.
- `scripts/check.sh` passes.
