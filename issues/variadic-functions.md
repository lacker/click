# Model variadic functions

C0 rejects `...` in a parameter list and has no representation for default
promotions, `va_list`, or `va_start`/`va_arg`/`va_end`.

## Violated invariant

Click should not claim a variadic call is safe without checking the promoted
argument types, the format or protocol governing the arguments, and the
callee's access to them.

## Intended regression

An unchanged variadic logging helper accepts a checked format contract and
reads its arguments safely. Negative tests reject a mismatched format and a
`va_arg` of the wrong promoted type.

## Acceptance criteria

- Variadic declarations, calls, and the `va_list` operations have a documented
  kernel model or a precise external-contract boundary.
- Argument promotions and format/protocol obligations are checked.
- The positive and negative regressions pass; `scripts/check.sh` passes.
