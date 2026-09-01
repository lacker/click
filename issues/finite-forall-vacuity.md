# Require vacuity outside the range in the FiniteForAll derivation rule

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced with
`click verify` (exit 0 on a universal that is false at k = 5).

The trusted checker for `PropositionDerivationRule::FiniteForAll`
(`src/kernel/assumptions.rs:2228-2233`) accepts `forall k: int32, body` when
`finite_forall_instantiations` yields a non-empty constant range and every
in-range instance checks. The range comes from `finite_forall_ranges`
(`src/kernel/reasoning/order_reasoning.rs:80-140`), which collects order facts
only through `collect_implication_antecedent_order_facts`
(`order_reasoning.rs:142-178`): it descends into the left side of `Implies`
and into `And`, `Or`, and `ForAll`, and treats a bare `ConditionIs` (and every
other proposition form) as a do-nothing arm. Nothing checks that the body is
vacuously true outside the intersected range, so a conjunct that is not an
implication, or a second implication with a wider guard, rides along
unchecked. `PureFactContext::proves_finite_forall`
(`src/kernel/assumptions/proposition_reasoning.rs:2843`) has the same shape.
The existing tests (`src/kernel/tests/proof_reasoning_tests.rs:3534`, `:3582`)
all use pure guard-implies-consequent bodies, which are sound.

## Violated invariant

`forall k, body` may be concluded from instances of `body` at every `k` in a
constant range `[lo, hi]` only if `body[k := c]` is true for every int32 `c`
outside `[lo, hi]`. A range derived from a guard justifies that vacuity only
for the implication that guard belongs to.

## Intended regression

```c
int32 identity(int32 x) { return x; }
```

```click
verifying "identity.c";
int32 identity(int32 x) {
    ensures bad: forall (k: int32) { ((0 <= k and k < 3) implies 0 <= k) and (k < 3) };
} by {
    step();
    have forall (k: int32) { ((0 <= k and k < 3) implies 0 <= k) and (k < 3) } by simp;
    simp();
}
```

Today this verifies. It must fail. A second regression with two guarded
implications of different widths, `forall k. ((0 <= k and k < 3) implies P(k))
and ((0 <= k and k < 10) implies Q(k))`, must fail unless `Q` is proved at 3
through 9. The control `ensures forall (k: int32) { k < 3 }` already fails and
must keep failing.

## Acceptance criteria

- `finite_forall_ranges` returns a range only when the whole body is
  established to be vacuous outside it: either every top-level conjunct is an
  implication whose antecedent entails membership in the returned range, or
  the rule checks each conjunct's own range separately and instantiates each
  at its own range.
- The trusted `FiniteForAll` checker in `assumptions.rs` enforces the same
  condition independently of the derivation producer, so a derivation object
  constructed by other kernel code cannot skip it.
- Kernel unit tests: the bare-conjunct body and the two-guard body are
  rejected; the guard-implies-consequent body still derives.
- Negative mdtests for both regressions; `scripts/check.sh` passes.

Related: [contract-finite-forall-premises.md](contract-finite-forall-premises.md)
is a second, independent finite-forall instantiator in contract certification
with a different defect. Consider merging both onto one sound implementation.
