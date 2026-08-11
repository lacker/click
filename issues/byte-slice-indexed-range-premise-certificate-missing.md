# Indexed-range premise instantiation has no explicit simple certificate

`mdtests/byte_slice_stdlib.md` fails ordinary verification:

```text
`byte_slice_facts.shifted_second_equal` path 0: smart `simp` closed the claim
but its certificate did not lower or replay: post-execution simplification
proved `p[2] == q[1]`, but Click has no explicit simple certificate for that
derivation
  selected premises: (0..2).all(k => p[(1 + k)] == q[(0 + k)])
```

Smart simplification instantiates the universal indexed-range premise
`(0..2).all(k => p[(1 + k)] == q[(0 + k)])` at `k == 1` and normalizes the
indices to reach `p[2] == q[1]`, but the certificate language has no simple
step that names a range-quantified premise, a witness index, and the
instantiated fact. This was previously tracked alongside the
owned-segmented-buffer order-weakening gap, but it is an independent problem:
the scalar order theorem (`int32_le_transitive`, landed) does not help here.
The missing vocabulary is universal-premise instantiation, the premise-side
dual of the universal-goal gap in
`universal-outcome-certificates-missing.md`.

## Reproduction

```sh
MDTEST_FILTER=byte_slice_stdlib.md cargo test --test mdtests
```

The mdtest is quarantined in `tests/mdtests.rs` until this is fixed.

## Acceptance criteria

- The unchanged `byte_slice_stdlib.md` mdtest passes and leaves quarantine.
- A focused regression expands a pointwise equality goal from a
  range-quantified `all` premise through an explicit instantiation step
  followed by `assumption`.
- The fix does not restore opaque certificates and does not widen an existing
  simple rule into a search.
