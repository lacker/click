# Tracing a function drops checked carrier dependencies

Priority: P1.

Soundness: incomplete. On the object-model recovery branch, a proof accepted by
ordinary verification, source-location verification, expansion and retained
rechecking is rejected by `--trace-proof` before the real failure frontier.
This reproduces inconsistent proof checking, not acceptance of a false claim.

Use the original [two-call C reduction](resource-unfold-after-call-rejects-checked-delta/repro.md)
after the declaration-based input observations and modular preservation repairs:

```sh
click verify bugs/resource-unfold-after-call-rejects-checked-delta/repro.md
click verify --trace-proof caller bugs/resource-unfold-after-call-rejects-checked-delta/repro.md
```

The first command verifies all three proofs. The second rejects
`fold(allocated(owner))` because it lacks the unchanged pointer field's complete
value equation. Selecting `caller.contract` through `verify_project_at`,
expanding it, checking the rewritten proof and rechecking a retained session
all pass with the same source and contracts.

The traced command calls `verify_project_functions` with a singleton set.
That API intentionally verifies its selected functions under callee contracts.
The source-location route uses `VerificationTarget::Function`, which obtains
checked carrier-producing callee proofs before checking the selected unit.
The traced command therefore loses an independently certified preservation
summary available to ordinary selected-proof checking.

Keep the contract-scoped function-set API's boundary. Route tracing through the
same proof-unit verification semantics as source-location checking; do not
verify the entire project as a workaround or broaden pointer address equality.

Acceptance criteria:

- The original reduction passes ordinary verification and `--trace-proof caller`.
- Source-location, expanded, rewritten and retained checking remain green.
- An unrelated failing proof is not added to the selected unit.
- Existing contract-scoped function-set clients retain their intended behavior.
- Trace rendering and fact selection keep their existing presentation design.
