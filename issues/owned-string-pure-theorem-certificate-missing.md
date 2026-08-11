# Owned-string pure theorem produces no pure surface certificate

`examples/owned-string` fails ordinary verification:

```text
smart proof for `pointer_add_zero_equals.ensures_0` succeeded but did not
produce a pure surface certificate
```

The pure-theorem gateway requires every smart pure proof to yield a complete
surface certificate, and `pointer_add_zero_equals` (a pointer-arithmetic
identity) has none. This is the pure-theorem analogue of the post-execution
certificate gaps: search succeeds through kernel reasoning that the pure
surface certificate generator cannot yet spell, likely a pointer-offset
normalization step with no named simple rule.

The violated invariant: a smart pure-theorem proof must produce a complete
pure surface certificate; success without one is an engine error (and is now
correctly reported as one).

## Reproduction

```sh
target/debug/click verify examples/owned-string
```

The project is quarantined in `tests/examples.rs` until this is fixed. A
reduced regression should state `pointer_add_zero_equals` (or the minimal
pointer-offset identity that reproduces the gap) as a standalone theorem in a
small sidecar.

## Acceptance criteria

- The unchanged owned-string project verifies and leaves quarantine.
- A focused pure-theorem regression expands the pointer identity through
  named simple steps and replays.
- The fix extends certificate vocabulary or generation; it does not weaken
  the gateway that reports missing certificates as errors.
