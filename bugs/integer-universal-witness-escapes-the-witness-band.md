# Integer universal witness escapes the witness band

Soundness: soundness-adjacent. No false acceptance is known. An Integer
`intro` that has to rename its binder takes the identity one above the
largest one its facts and body mention. That identity can land in another
producer's band: for example, it can be an identity `is_load_variable`
accepts. It can also equal a live C-state identity that no fact mentions.
The int32, algebraic and pointer introductions take their witness from the
reserved universal-witness band.

## Violated invariant

`ProofFacts::fresh_universal_witness` in `src/kernel/proof/facts.rs`
documents the rule. A universal introduction's witness comes from
`ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_BASE..CEILING`, because "the
facts are not the whole state a witness has to stay clear of": a C proof also
carries program variables, a symbolic store, a memory snapshot and a resource
context. The same comment calls "scan for an identity no fact mentions" the
earlier, wrong rule. `freshen_int32_forall_body`, `freshen_algebraic_forall_body`
and `freshen_pointer_forall_body` follow the band rule.
`freshen_integer_forall_body` (called from `src/kernel/proof/object.rs`,
`Sort::Integer`) still computes `max(reserved ∪ body) + 1` and probes upward
against facts and body only.

## Reproduction

Reproduced on master `da7834d2`, as a test added to
`src/kernel/proof/facts.rs`:

```rust
#[test]
fn integer_universal_witnesses_come_from_the_witness_band() {
    let binder = Variable(3_200_000);
    let load = Variable((1 << 40) + 7);
    let integer_fact = |variable| {
        Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                crate::kernel::IntegerTerm::var(variable).into(),
                crate::kernel::IntegerTerm::constant_i64(0).into(),
            ),
            true,
        )
    };
    let facts = ProofFacts::from_ordered(&[
        Proposition::ConditionIs(
            ConditionTerm::equal(Bitvector32Term::Variable(load), Bitvector32Term::Constant(0)),
            true,
        ),
        integer_fact(binder),
    ]);
    let body = integer_fact(binder);
    let (witness, _) = facts.freshen_integer_forall_body(binder, &body).unwrap();
    assert!(crate::kernel::ExecutionBudget::is_universal_witness_variable(witness));
}
```

The witness is `Variable(1099511627784)`, which is `(1 << 40) + 8`, and
`is_load_variable` accepts it. On the same facts, `freshen_int32_forall_body`
returns `Variable(4398046511104)`, the first witness-band identity.

## Related site

Integer `choose` and `obtain` (`check_integer_choice` and
`check_exists_bindings` in `src/kernel/proof/object.rs`) use the same rule.
They start from a hint the surface supplies, at `3_000_000`, inside the
quantifier band, and probe upward against facts, goal and body only. These
were not reproduced separately. Check them when this is fixed.

## Acceptance criteria

- `freshen_integer_forall_body` takes its witness from the universal-witness
  band, as its siblings do.
- The test above passes.
- The choice sites are either moved to the band or shown not to need it, with
  a note here or a regression test.
