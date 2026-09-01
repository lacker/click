# Stop trusting caller-supplied contract structure in rule certification

Found by the 2026-09-01 kernel audit at cb034b21. None of these reach a false
verdict through the shipped CLI today: the surface lowering emits complete
claim lists (item 1), and the two fact shapes item 2 admits are exactly the
ones the surface passes as `derived_entry_facts` (sized-array loadability from
declared parameter forms, `src/surface/verification.rs:960-975`, and
surface-verified theorem implications, `verification.rs:700-718`, `:949-953`,
`:1016-1020`), so their truth currently rests on the surface verifier rather
than on kernel certification. All three are also reachable through the public
kernel API, which the kernel's own comments treat as inside its threat model.

1. **Claim coverage.** `c_verified_function_rule`
   (`src/kernel/api/contract_certification/contract_claims.rs:1705-1720`)
   checks only that every entry of `function.contract_claims()` has a matching
   `CVerifiedFunctionContractClaim`. Nothing checks that the claim list covers
   every `contract_ensures()` and `resource_ensures()` index. Rule application
   ignores the claim list: `add_verified_function_ensure_facts`
   (`src/kernel/functions.rs:1019-1051`) pushes every ensure as
   `ExecutionPureFact::certified` and `evaluate_function_return_resources`
   (`functions.rs:1792`) grants every resource ensure; `execute_verified_function_rule`
   never reads `contract_claims`. A `BodySafety`-only claim list (which
   returns true on every prepared path, `contract_claims.rs:1053`) packages a
   rule for any false ensure. `CFunction::with_contract`
   (`src/kernel/primitives/contracts.rs:60`) accepts any claim list.
2. **Injected entry facts.** `c_function_contract_certification_assumptions`
   (`src/kernel/api/contract_certification.rs:868-882`) copies every
   `CMemoryLoadable` fact and every `forall .. -> .. -> Predicate` fact from
   the caller-supplied `derived_entry_facts` (`src/kernel/api.rs:2993`)
   straight into the assumption base before the derived-fact certification
   loop (`api.rs:3117-3185`) runs. The API doc at `api.rs:2924-2927` states
   callers cannot inject hypotheses; for these two shapes that is false, and
   the hypothesis is not recorded on the resulting rule.
3. **Guarded mutable segments.** Certification admits a guarded segment into
   the write set unless `evaluate_guarded_contract_condition` returns
   `Some(false)` (undecided is included, `contract_claims.rs:1255-1264`),
   while call-site havoc skips the segment whenever the guard is provably
   false (`functions.rs:751-760`). A callee whose write is covered only by a
   guard-undecided segment certifies; a guard-false caller applies the rule
   with no havoc. The surface builds guarded segments from conditional
   composite resource bodies (`src/surface/lowering/annotations.rs:511-518`,
   `:552-563`), but certification case-splits entry on those same resource
   conditions through `contract_resource_condition_cases` (`api.rs:3028`), so
   only a guard supplied directly through `CMemorySegment::with_guard` on the
   kernel API reaches the undecided branch.

## Violated invariant

A `CVerifiedFunctionRule` may publish only consequences that a kernel-produced
execution frontier certified: every `ensures`, every `resource_ensures`, and
the mutable frame. The certification assumption base is derived solely from
the exact contract and entry state; caller-supplied facts enter only after
kernel certification. The write set a callee is certified against must be the
write set a caller havocs.

## Intended regression

Kernel tests against the public API:

1. `int32 callee() { return 1; }` with `contract_ensures = [result == 0]` and
   `claims = [body_safety()]` (and separately `ensures = [A, B]` with a claim
   for `A` only). Today `c_verified_function_rule` packages a rule; it must
   return `None` and `c_unverified_function_contract_claims` must name the
   uncovered ensure. Mirror `src/kernel/tests/contract_execution_tests.rs:1165`.
2. `int32 f(int32 x) { return 0; }` with `ensures P(result)` for an opaque
   predicate `P` registered as `x >= 1`, and
   `derived_entry_facts = [forall x. P(x)]`. Today the claim certifies; it must
   not, or the injected fact must appear as an explicit rule hypothesis.
3. Callee with `mutable p[0..1] when flag != 0` that unconditionally writes
   `p[0]`; caller with `flag == 0` applying the rule must not be able to prove
   `p[0]` unchanged.

## Acceptance criteria

- `c_verified_function_rule` and `c_recursive_function_contract_hypothesis`
  require an `EnsureProposition` claim for every ensure index, an
  `EnsureResource` claim for every resource-ensure index, and `Effect`
  coverage for the mutable frame.
- The two assumed fact shapes at `contract_certification.rs:872-879` are
  admitted only through the derived-fact certification loop (resource check
  for loadables, kernel pure-theorem authority for quantified predicate
  implications), and the API doc becomes true.
- Guarded segments are certified under the same semantics they are applied
  under: excluded unless the guard is provably true on the path, or
  case-split as `contract_resource_condition_cases` does.
- The three kernel tests above; `scripts/check.sh` passes.
