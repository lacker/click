# Pointer effects can specialize caller entry cells

Body-certified pointer result and stored-carrier effects currently reuse the
execution artifact's caller memory. Independent symbolic parameter values do
not make its preexisting cell contents universal contract inputs.

## Reproduction

Run the kernel unit regression
`specialized_entry_pointer_cell_cannot_certify_parameter_transport` in
`src/kernel/functions/pointer_result_effect_tests.rs`. The corrected fixture
passes independent symbolic `p` and `q`, declares `p` as a record with pointer
member `kid`, supplies its owned bytes, and prepopulates `p.kid` with the full
semantic `q` carrier. The function returns `p.kid`; a second case first stores
`p.kid` back into itself. Its interface promises neither equality nor semantic
identity between the member and `q`.

The regression failed in the compiled `tests14` checkpoint at the assertion
that this caller-specific cell cannot certify a universal parameter
relationship. The ordinary direct `p.kid = q` positive passed in the same run.

## Cause

`prepare_function_claim_path` reconstructs entry through
`c_function_entry_state_with_assumptions`, whose argument binder clones the
artifact caller's memory. Effect inference checks symbolic parameter
independence but then observes the specialized cached cell. A successful
checked execution under that state does not certify the inferred relationship
for every call satisfying the function interface.

## Acceptance

- Infer transport and native output authority only from independently checked
  universal contract entry construction, using the same argument identities.
- Refuse additional caller cell values or entry facts as reusable authority.
- Reject both original loaded-return and self-store regressions.
- Preserve direct parameter identity, direct parameter member stores, and
  supported native construction into an independent hidden destination.
- Keep opaque unresolved-result markers available without granting validity.
- Do not infer semantic designation from numeric pointer equalities or scan
  unrelated ambient memory to guess universality.
