# Check every premise in contract certification's finite-forall instantiator

Found by the 2026-09-01 kernel audit at cb034b21. Confirmed by a kernel-API
probe that minted a `CVerifiedFunctionRule` asserting `vac(n) == 7` for
`int32 vac(int32 n) { return n; }`.

`finite_forall_instantiations` in
`src/kernel/api/contract_certification.rs:1699-1741` splits an assumed
`forall x. A1 -> A2 -> ... -> P` into premises, takes the constant bounds
`(lo, hi)` from the first premise that `constant_variable_bounds` parses
(`find_map`, line 1717), and then at every witness treats any premise that
`constant_variable_bounds` parses as satisfied without evaluating it
(`.is_some() ||` at line 1727). Only non-bound premises go through
`constant_premise_value`. The bare conclusion `P[c/x]` is then added as a
path fact with all premises stripped. A second, disjoint constant-bound
premise is never checked. `function_claim_holds_on_prepared_path`
(`src/kernel/api/contract_certification/contract_claims.rs:1137-1141`)
extends path assumptions with these instances before
`certification_proves_post_proposition`, and the `checked_propositions`
shortcut is or-ed before it, so the kernel certifies with no surface evidence
at all. `c_unverified_function_contract_claims` reports nothing unverified for
this contract.

This instantiator is distinct from `PureFactContext::finite_forall_instantiations`
(`src/kernel/assumptions/proposition_reasoning.rs`), which instantiates the
whole body including its premises and is sound on this point.

The shipped CLI is shielded only because `src/surface/verification.rs` calls
`c_verified_function_contract_claims_with_checked_propositions` after every
ensure has a surface proof, and the surface's own closers use the sound
instantiator. That shield is untrusted code, and the kernel API is exposed
regardless of it. [double-execution.md](double-execution.md) plans to delete
the independent-execution fallback in claim finishing, which is the path this
instantiator runs on; fix or delete the instantiator so it cannot outlive that
removal.

## Violated invariant

An instance `P[c/x]` of an assumed universal may be added as a certification
fact only if every premise of the universal holds at `c`.

## Intended regression

Kernel test against the public API:

```text
requires = ForAllInt32 k. (0 <= k and k < 3) -> ((5 <= k and k < 10) -> n == 7)
ensures  = result == 7
function = int32 vac(int32 n) { return n; }   // claims: ensure_proposition(0, 0)
```

Run `prove_c_function_contract_execution_paths_with_environment` with a
symbolic argument, then `c_verified_function_contract_claims` and
`c_verified_function_rule`. Today the claim certifies and the rule is minted.
After the fix `c_verified_function_contract_claims` must return `None` (or the
claim must be reported unverified) and no rule may be constructed. Mirror the
existing test at `src/kernel/tests/contract_execution_tests.rs:1165`.

Sidecar form for a positive mdtest once the surface can state it:
`requires forall (k: int32) { (0 <= k and k < 3) implies ((5 <= k and k < 10)
implies n == 7) }; ensures result == 7 by auto;` must fail at certification,
not only in the surface.

## Acceptance criteria

- At line 1727 the `constant_variable_bounds(...).is_some() ||` shortcut is
  removed; every premise, bound-shaped or not, must evaluate to `Some(true)`
  after substitution before an instance is admitted (or all bound premises
  are merged into one `(lo, hi)` by max/min before iteration).
- The kernel test above is added and passes; the two-premise tautology
  certifies nothing.
- `c_unverified_function_contract_claims` reports the ensure as unverified for
  the regression contract.
- Prefer sharing one finite-forall instantiator between contract certification
  and `PureFactContext`; if two remain, a unit test pins that they agree on
  the regression bodies.
- `scripts/check.sh` passes.

Related: [finite-forall-vacuity.md](finite-forall-vacuity.md).
