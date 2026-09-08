# Model signed eight-bit integers

## Violated invariant

The initial kernel target intentionally gives plain `char` unsigned semantics,
but C `signed char` and `int8_t` still have no modeled scalar or pointer type.
They cannot be aliases of the unsigned-byte type: loads and promotions must
interpret high-bit values as negative. This does not block unsigned plain char.

## Intended regression

Prove `signed char x = -1; return x;` returns -1 after promotion to int, not
255. Cover loads/stores, arrays, global/static storage, calls, const views, and
conversion boundaries at -128 and 127. Reject false unsigned interpretations
and out-of-range operations under the declared implementation rules.

## Acceptance criteria

- Carry signed-byte values and promotions through C syntax, sidecars, lowering,
  memory, and kernel checking, including supported explicit conversions.
- Keep plain char, signed char, and unsigned char distinct for source-level
  compatibility even when a target chooses matching representations.
- Add positive and negative kernel/fixture coverage and pass `scripts/check.sh`.
- Supporting signed plain char on another target is separate profile work in
  `multiple-compilers.md`; do not silently change the initial kernel target.
