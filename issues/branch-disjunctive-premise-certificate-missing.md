# Disjunctive premise case split has no explicit simple certificate

`mdtests/proof_branch_pointer_local.md` fails ordinary verification:

```text
`advance_selected_pointer.ensures_0` path 0: smart `simp` closed the claim
but its certificate did not lower or replay: post-execution simplification
proved `(result == left[0] || result == right[0])`, but Click has no explicit
simple certificate for that derivation
  selected premises: at(statement(4).exit, (selected == left || selected == right))
```

Smart simplification case-splits on the point-qualified disjunctive premise
`selected == left || selected == right` and, in each case, transports the
load `selected[0]` to the matching input pointer to certify one side of the
disjunctive goal. The certificate language has no simple step for eliminating
a disjunctive premise into per-case subproofs (or for introducing a chosen
disjunct of a disjunctive goal). This was previously tracked alongside the
owned-segmented-buffer order-weakening gap, but it is an independent problem:
the scalar order theorem (`int32_le_transitive`, landed) does not help here.

## Reproduction

```sh
MDTEST_FILTER=proof_branch_pointer_local.md cargo test --test mdtests
```

The mdtest is quarantined in `tests/mdtests.rs` until this is fixed.

## Acceptance criteria

- The unchanged `proof_branch_pointer_local.md` mdtest passes and leaves
  quarantine.
- A focused regression expands a disjunctive goal from a disjunctive premise
  through explicit case-elimination and disjunct-introduction steps.
- The fix does not restore opaque certificates and does not widen an existing
  simple rule into a search.
