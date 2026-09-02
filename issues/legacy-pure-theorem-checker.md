# Route induction proofs through the kernel proof object

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced with
`click verify` (exit 0) on a pure theorem that is false at `y = 3`.

For any theorem with an `induction_setup`, both acceptance
(`src/surface/proof/pure_theorems.rs:545-575`) and the certificate round trip
(`validate_pure_theorem_certificate`, `pure_theorems.rs:2199-2241`) go through
`prove_pure_theorem_script`, the legacy surface checker; no kernel proof step
participates. `kernel_authority` (`pure_theorems.rs:621-660`) is derived
independently of the script by `prove_universally_quantified_pure_implication`,
which fails for this theorem, so it is published with no kernel authority. That checker's `Intro`
(`src/surface/proof.rs:168-171`) does `*goal = *body` with no fresh variable,
leaving the binder free in `available`; its `Have`
(`pure_theorems.rs:3036-3075`) opens `Proof::for_pure_goal` with those
captured facts as requirements, and the nested `have` goal re-lowers its own
binder to the same id; its `Assumption`
(`pure_theorems.rs:3140-3150`) closes through
`quantified_equivalent_available_fact` (mutual `derive_simp_proposition`
derivability between two `forall` facts,
`src/kernel/proof/fact_reasoning.rs:868-888`). The false theorem
is then published to `TheoremEnvironment` and `theorem_certification_facts`
(`src/surface/verification.rs:690-725`).

Escalation to a false C verdict was attempted and blocked: kernel contract
certification assumes derived facts only after re-certifying them
(`src/kernel/api.rs:3148-3180`). Any surface-trusted contract path would
escalate it, and the theorem is applicable in every surface proof.

## Violated invariant

A verified pure theorem's `requires -> ensures` must hold for all parameter
values, and the authority for that must be a kernel-checked derivation. No
proof route may accept a theorem without kernel involvement.

## Intended regression

```click
theorem capture(n: int32) {
    requires n >= 0;
    ensures forall (x: int32) { x == 5 implies forall (y: int32) { y == 5 } }
    by { induct(n) as ih; intro(); intro();
         have forall (z: int32) { z == 5 } by { intro(); assumption(); }
         assumption(); }
}
```

Today `click verify` exits 0. It must fail at the inner `have`. Controls that
already fail and must keep failing: the same script without `induct` (rejected
at the kernel round trip because pure `assumption` is exact), without the
`have`, with `y == 6`, and with no outer intros.

## Acceptance criteria

- Induction proofs are checked by the kernel `ProofObject` like every other
  pure proof; the legacy `prove_pure_theorem_script` is either removed or
  reduced to a presentation-only walk whose verdict is not authoritative.
- If any script shape still falls to the legacy checker, its `Intro`
  freshens the binder against `available` and its `Assumption` uses the same
  exactness rule as the kernel's pure context (`src/kernel/proof/object.rs:566-571`),
  and a test pins that the legacy and kernel checkers agree on the regression.
- `kernel_authority` is `Some` for every theorem published to
  `TheoremEnvironment`, or theorems without it are not published as
  certification facts.
- Negative mdtest for the regression; `scripts/check.sh` passes.
