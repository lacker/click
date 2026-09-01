# Enforce binder freshness and simultaneous substitution in the kernel

Found by the 2026-09-01 kernel audit at cb034b21. One item here (sequential
substitution) mints a false claim through the public kernel API with only
true inputs; the others are real defects held back by an unenforced numbering
convention.

Fresh variables come from disjoint numeric bands: C parameters `0..n`
(`src/surface/lowering/resource_lowering.rs:47-56`); kernel-fresh variables
from 1_000_000 (`src/kernel/primitives/derivations.rs:709`, `src/kernel/api.rs:428`);
fixed-state lowering binders restarting at 2_000_000 per proposition
(`src/surface/lowering/proposition_lowering.rs:30`,
`src/surface/proof/fixed_state_proofs/have_proofs.rs:107`); body and
annotation binders from 3_000_000 (`src/surface/lowering/annotations.rs:174`);
contract binders from 3_100_000 (`annotations.rs:293`); composite-resource
condition binders from 3_200_000 (`annotations.rs:47`); `choose` witnesses
from 3_000_000 (`src/surface/proof/proof_object.rs:836`, consumed at
`src/surface/proof/proof_object/fixed_state_steps.rs:275`); hash-derived fold
binders anywhere in 3_000_000..1_003_000_000 (`src/kernel/spec.rs:1728-1735`,
`src/surface/lowering/proposition_lowering.rs:967-975`); load variables at
2^40. Nothing checks the bands, and
`collect_spec_proposition_bitvector_variables` deliberately removes binders
from the reservation set (`src/kernel/reasoning/variable_collection.rs:488`).
At least five independent substitution or alpha-equivalence implementations
exist. Three kernel-side defects depend on this:

1. **Sequential substitution.**
   `certification_proves_predicate_from_quantified_implication`
   (`src/kernel/api/contract_certification.rs:2738-2815`, loop at `:2806-2812`)
   collects `[(x0, t0), (x1, t1)]` and applies plain replace-all substitution
   one pair at a time on the already-rewritten premise, so if `t0` mentions
   `Variable(1)` it is rewritten to `t1`. Theorem facts use binders
   `Variable(index)` (`src/surface/verification.rs:705-715`) and int32
   parameters are `Variable(position)`, so the ids coincide. Goal `P(n, m)`
   against fact `forall v0 v1. v0 == 5 -> P(v0, v1)` rewrites the premise to
   the function's own `requires m == 5` and certifies the false
   `ensures P(n, m)`. The same loop in
   `certification_proves_condition_from_verified_pure_implication`
   (`:2668-2676`) discharges path obligations at `src/kernel/api.rs:3491`.
   Surface `apply` instantiates by name and never calls these, which is the
   only reason the CLI rejects the sidecar form.
2. **One-sided alpha-equivalence.** `propositions_alpha_equivalent`
   (`contract_certification.rs:1745-1793`) and three sibling renames
   (`:317-364`, `:2360-2405`, `:2822-2878`;
   `src/kernel/assumptions/proposition_reasoning.rs:850-860`, `:975-990`)
   substitute the fact's binder with the goal's binder and compare
   structurally, with no check that the goal binder is not already free in
   the fact body. `forall x. (y == 5)` with `x` unused would match
   `forall y. (y == 5)`. Every call site puts the fact on the left, so a weak
   fact could discharge a strong goal.
3. **RangeFold substitution is not capture-avoiding.** The RangeFold arm of
   the term-level `substitute_bitvector_variable`
   (`src/kernel/reasoning/substitution.rs:1696-1717`, called from
   `substitute_bitvector_variable_in_proposition`) omits the renaming the
   ForAll and Exists arms of the proposition-level function (`:349`, `:364`)
   do through `capture_avoiding_quantifier_body`. A fold item name whose
   FNV-1a hash lands on `Variable(3000000)`, the `choose` witness base (for
   example `afrls0v`), lets a `have` accept the false lemma
   `(0..n).fold(0, |acc, afrls0v| acc + afrls0v * afrls0v) == 6` by capture;
   only the independent re-execution of the ensures stopped it.

A usability symptom of the same scheme: a `have` stating the second
quantified conjunct of a goal like `(forall x. P) and (forall y. Q)` lowers
`y` as `Variable(2_000_000)` while the goal's `y` is `Variable(2_000_001)`,
so kernel `split` and exact `assumption` miss
(`src/kernel/proof/object.rs:668`).

## Violated invariant

Instantiating `forall x0 x1. Pre -> Pred` at arguments must substitute
simultaneously (or rename binders to variables fresh with respect to fact,
goal, and assumptions first). Two quantified propositions are alpha-equivalent
only if renaming apart is capture-free. Every substitution into a binder,
including RangeFold, must be capture-avoiding. Freshness must be checked, not
assumed from a numeric band.

## Intended regression

Kernel tests, one per defect:

1. Theorem `forall v0 v1. v0 == 5 -> is_five(v0, v1)` proved through
   `prove_universally_quantified_pure_implication`; function
   `int32 f(int32 m, int32 n) { return 0; }` with `requires m == 5` and
   `ensures is_five(n, m)` where `is_five(a, b) := a == 5`. Today
   `c_verified_function_contract_claims` certifies the ensure; it must not.
2. `propositions_alpha_equivalent(forall x. (y == 5), forall y. (y == 5))`
   with `x` unused must return `false`.
3. Substituting a term containing the fold item variable into a RangeFold
   body must rename the item, matching the ForAll test at
   `src/kernel/tests/proof_reasoning_tests.rs:3311`.

## Acceptance criteria

- Both quantified-implication certifiers substitute simultaneously.
- Alpha-equivalence renames both sides to a fresh variable or checks
  freshness before renaming, in all six sites.
- The RangeFold substitution arm is capture-avoiding.
- One shared, tested alpha-equivalence and substitution implementation is
  used by `contract_certification.rs`, `fact_keys.rs`, and `substitution.rs`,
  or a test pins that the remaining implementations agree on a corpus of
  binder-collision cases.
- Fresh-variable allocation across the surface lowerers and the kernel checks
  against a shared reservation set rather than relying on bands; the
  `split`/`assumption` symptom above verifies.
- `scripts/check.sh` passes.

Related: [have-binder-capture.md](have-binder-capture.md),
[surface-substitution-capture.md](surface-substitution-capture.md),
[legacy-pure-theorem-checker.md](legacy-pure-theorem-checker.md).
