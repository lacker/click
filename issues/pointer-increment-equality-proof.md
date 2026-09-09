# Construct the pointer-increment equality proof found by simp

## Violated invariant

A smart derivation must be representable by an explicit checked proof object.
Pointer equality reasoning currently finds a derivation that the surface
simple-proof emitter cannot express. Verification rejects it rather than
silently accepting success without a proof, but this blocks loop migration.

## Reproduction

Keep the C and invariants in `mdtests/c_pointer_local_loop_invariant.md`
unchanged. Add this preservation body after `invariant p == arr + i;`:

```click
preserve by {
    step(); step();
    have p == arr + i by simp;
    close_invariants();
}
```

The loop increments the index and pointer independently. The previous
`p == arr + i` relation and the loop condition should connect the resulting
pointer expressions, with checked integer-definedness evidence where needed.
The diagnostic says smart reasoning found a derivation but has no explicit
simple certificate for pointer equality. Its selected premises are the
loop-entry `i < n` and `p == arr + i` facts.

`pointer_loop_increment_reports_missing_simple_equality_proof` keeps this
failure executable on the normal production path, independently of the staged
automatic-closure migration. It checks the specific local error and never
expands the failing proof.

## Next investigation

Trace the selected pointer-equality derivation to the simple-proof emitter.
Determine whether an existing checked pointer rule lacks emission or whether
execution failed to retain the necessary relation/definedness evidence.
Do not broaden search, modify the C, weaken the invariants, or reinstate a
success-without-proof fallback.

## Acceptance criteria

- The unchanged C and explicit preservation proof verify.
- Expansion produces an independently verifying simple proof, including
  required pointer/index and integer-definedness premises.
- Missing relation and possible overflowing index variants reject.
- Change the expected-gap test into positive verification/expansion/recheck
  coverage; preserve bounded, output-sensitive simple checking.
- `scripts/check.sh` passes; remove this issue and its index entry.
