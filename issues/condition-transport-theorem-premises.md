# Retain contextual premises in condition-transport theorems

P1: a public kernel API exports a false context-free `Theorem`.
Reproduced at `3ad0d2e1` using only public library APIs. A false CLI contract
through this particular route was not established.

## Violated invariant

Every `Theorem` must be valid as the proposition it exports. A theorem
constructor using contextual assumptions must retain or discharge them;
arbitrary `PureFactContext` entries are not unconditional theorem authority.

`prove_c_condition_fact_target_transport` in `src/kernel/api.rs` proves its
target under `assumptions + source`, then constructs only `source => target`.
`Theorem` in `src/kernel/primitives.rs` stores only the exported proposition,
with no hidden context. Other theorem constructors use `wrap_proof_facts`
to retain premises.

## Small reproduction

The following temporary integration test compiles against the public API:

```rust
use click::kernel::*;

#[test]
fn contextual_transport_exports_false_theorem() {
    let source = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let target = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    let context = PureFactContext::new().assume_proposition(target.clone());
    let theorem = prove_c_condition_fact_target_transport(&source, &target, &context)
        .expect("supplied contextual assumption gets accepted");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(source), Box::new(target)),
    );
}
```

The test passes: the kernel exports `true => false`. It should instead reject
the requested closed theorem or expose the false premise in the result.

The problem also occurs with a consistent context. Replace `target` with:

```rust
let target = Proposition::ConditionIs(
    ConditionTerm::Bitvector32Equal(
        Box::new(Bitvector32Term::Variable(Variable(777))),
        Box::new(Bitvector32Term::Constant(0)),
    ),
    true,
);
```

An empty context returns `None`, but assuming `x == 0` produces the exported
theorem `true => x == 0`, without its premise. That proposition is false at
`x = 1`.

The current surface consumer in
`src/surface/proof/fixed_state_proofs/fact_transport.rs` uses the result
inside the same ambient context. This limits the demonstrated CLI impact,
but does not repair the public kernel authority boundary.

## Acceptance criteria

- Neither reproduction may produce its current unconditional theorem.
  Retain the consumed premises, discharge them with checked evidence, or
  return a context-bound evidence type instead of a closed `Theorem`.
- Audit `prove_c_condition_fact_transport`,
  `prove_c_condition_fact_direct_transport`, and
  `prove_c_condition_fact_transport_with_assumptions` in
  `src/kernel/memory_provenance.rs` for the same premise-loss pattern.
- Preserve exact premise provenance without cloning or scanning unrelated
  proof context; cover any representation change with deterministic scaling
  regressions.
- Retain valid disjoint-memory transport and other positive callers, and
  add public API regressions for both inconsistent and consistent contexts.
- `scripts/check.sh` passes.
