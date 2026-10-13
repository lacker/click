# Unchanged pcg-c-basic source

This project preserves `pcg_basic.c`, `pcg_basic.h` and `LICENSE.txt`
byte-for-byte from pcg-c-basic at revision
`bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3`:

<https://github.com/imneme/pcg-c-basic/tree/bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3>

status: verified

`SOURCE.sha256` pins all three files; the examples gate checks it before
verifying. The code is Apache-2.0 licensed (`LICENSE.txt`).

`pcg_basic.click` proves, for Click's default x86-64 Linux user-space target:

- `pcg32_random_r` advances the state by the 64-bit LCG step
  `state * 6364136223846793005 + inc` (wrapping), leaves `inc` unchanged, and
  returns the XSH-RR output of the old state, including the rotation by
  `(-rot) & 31`.
- `pcg32_srandom_r` leaves `inc` odd as `(initseq << 1) | 1` and the state as
  the value its two generator calls produce from zero.
- The public wrappers `pcg32_srandom` and `pcg32_random` pass the file's
  private `pcg32_global` to those helpers; their contracts own its fields by
  name and state the same effects on it.

`pcg32_boundedrand_r` and `pcg32_boundedrand` are imported but not specified:
their retry loop terminates only with probability one.

A client checking the first two outputs after `pcg32_srandom(42, 54)`
(`0xa15c02b7`, `0x7b47f409`) and that reseeding repeats them is the remaining
acceptance work in `issues/private-static-helper-ownership.md`. Evaluating the
output formula on the seeded state is blocked by
`bugs/normalize-leaves-an-unsigned-shift-by-a-folded-amount-unevaluated.md`.
